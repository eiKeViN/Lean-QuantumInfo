/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat
open scoped InnerProductSpace RealInnerProductSpace

/-! Lieb's Inequality .. todo -/

variable {m n : Type*} [Fintype m] [Fintype n] {q r : ℝ}

noncomputable section
open ComplexOrder
open Classical



/-! Need to define the space of (semi)positive definite hermitian matrices)-/
theorem PowerMeanConcavity {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
  let Fb : (HermitianMat n ℂ × HermitianMat n ℂ) → HermitianMat n ℂ :=
      fun (x, y) => y.conj (x ^ (-b/2));
  let Fab : (HermitianMat n ℂ × HermitianMat n ℂ) → HermitianMat n ℂ :=
      fun (x, y) => ((Fb (x, y)) ^ a).conj (x ^ (b / 2));
    ConcaveOn ℝ .univ Fab := by
  sorry

theorem LiebConcavity' (K : Matrix n n ℂ) (hq : 0 < q) (hr : 0 < r) (hqr : q + r ≤ 1) :
  let F : (HermitianMat n ℂ × HermitianMat n ℂ) → ℝ :=
      fun (x, y) => ⟪((x ^ q).conj K), (y ^ r)⟫;
    ConcaveOn ℝ .univ F := by
  sorry

theorem LiebConcavity (K : Matrix n m ℂ) (hq : 0 ≤ q) (hr : 0 ≤ r) (hqr : q + r ≤ 1) :
  let F : (HermitianMat m ℂ × HermitianMat n ℂ) → ℝ :=
      fun (x, y) ↦ ⟪((x ^ q).conj K), (y ^ r)⟫;
    ConcaveOn ℝ .univ F := by
  sorry

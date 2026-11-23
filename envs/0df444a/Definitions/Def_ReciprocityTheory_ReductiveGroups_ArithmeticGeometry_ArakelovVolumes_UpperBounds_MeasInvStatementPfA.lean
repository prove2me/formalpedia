-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:38.135314+00:00
-- url     : https://prove2.me/theorems/39a4e32e-5963-4244-ad50-19b1b7dd768d
-- title:
--   Meas Inv Statement Pf A
-- statement:
--   Definitions and structural lemmas for Meas Inv Statement Pf A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
abbrev Ix (ι : Type*) (r : ℕ) : Type _ := ι × Fin r × Fin r
def sl (w : Ix ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if b < a then w (τ, a, b) else 0
def up (w : Ix ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if b < a then 0 else w (τ, a, b)
def lu (w : Ix ι r → ℂ) : Ix ι r → ℂ := fun i => ((1 + sl w i.1) * up w i.1) i.2.1 i.2.2
lemma sl_add (h h' : Ix ι r → ℂ) (τ : ι) : sl (h + h') τ = sl h τ + sl h' τ := by
  ext a b
  simp only [sl, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp
lemma up_add (h h' : Ix ι r → ℂ) (τ : ι) : up (h + h') τ = up h τ + up h' τ := by
  ext a b
  simp only [up, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp
lemma sl_smul (c : ℂ) (h : Ix ι r → ℂ) (τ : ι) : sl (c • h) τ = c • sl h τ := by
  ext a b
  simp only [sl, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp
lemma up_smul (c : ℂ) (h : Ix ι r → ℂ) (τ : ι) : up (c • h) τ = c • up h τ := by
  ext a b
  simp only [up, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp
def luD (w : Ix ι r → ℂ) : (Ix ι r → ℂ) →ₗ[ℂ] (Ix ι r → ℂ) where
  toFun h i := (sl h i.1 * up w i.1 + (1 + sl w i.1) * up h i.1) i.2.1 i.2.2
  map_add' h h' := by
    funext i
    simp only [sl_add, up_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_apply, Pi.add_apply]
    ring
  map_smul' c h := by
    funext i
    simp only [sl_smul, up_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Pi.smul_apply, RingHom.id_apply]
    ring
def key (e : ι ≃ Fin (Fintype.card ι)) (i : Ix ι r) : ℕ ×ₗ (ℕ ×ₗ Fin (Fintype.card ι)) :=
  toLex ((i.2.1 : ℕ) + i.2.2, toLex ((i.2.1 : ℕ), e i.1))
def luD' (w : Ix ι r → ℂ) : (Ix ι r → ℂ) →L[ℝ] (Ix ι r → ℂ) :=
  LinearMap.toContinuousLinearMap ((luD w).restrictScalars ℝ)
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI



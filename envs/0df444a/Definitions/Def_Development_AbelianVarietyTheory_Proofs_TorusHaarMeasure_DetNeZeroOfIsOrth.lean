-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:39.642553+00:00
-- url     : https://prove2.me/theorems/12889107-d8aa-4dc6-b527-8236f38c5981
-- title:
--   Det Ne Zero Of Is Orth
-- statement:
--   Definitions and structural lemmas for Det Ne Zero Of Is Orth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DetNeZeroOfIsOrth.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate
namespace GlobalTheory.UnitaryFrames
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E] in
lemma gram_eq_mul {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G P = Pᵀ * (G.map τ * P.map (starRingEnd ℂ)) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, mul_assoc]
lemma det_ne_zero_of_isOrth {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x)
    (τ : X.Ψ) : (mat x τ).det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det (hx τ)
  rw [gram_eq_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, Matrix.det_diagonal] at h
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
  unfold sgn
  split_ifs <;> simp
def unitarySubgroup {r : ℕ} (X : Data E r) : Subgroup (X.Ψ → GL (Fin r) ℂ) where
  carrier := {g | X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)}
  one_mem' := by
    intro τ u w
    simp
  mul_mem' := by
    intro a b ha hb τ u w
    have h1 := ha τ ((b τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ u) ((b τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ w)
    have h2 := hb τ u w
    simp only [Matrix.mulVec_mulVec] at h1
    simp only [Pi.mul_apply, Units.val_mul]
    exact h1.trans h2
  inv_mem' := by
    intro a ha τ u w
    have h1 := ha τ ((((a τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ u)
      ((((a τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ w)
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h1
    exact h1.symm
noncomputable def toGL {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) :
    X.Ψ → GL (Fin r) ℂ :=
  fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (mat x τ) (det_ne_zero_of_isOrth X hx τ)
end GlobalTheory.UnitaryFrames



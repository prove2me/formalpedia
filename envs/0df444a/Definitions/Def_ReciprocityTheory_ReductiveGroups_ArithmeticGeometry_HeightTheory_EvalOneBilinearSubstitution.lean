-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_EvalOneBilinearSubstitution
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_EvalOneBilinearSubstitution
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:19.660863+00:00
-- url     : https://prove2.me/theorems/7c921ef3-81f7-4a61-a297-85f0bf6dca0f
-- title:
--   Eval One Bilinear Substitution
-- statement:
--   Definitions and structural lemmas for Eval One Bilinear Substitution, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/EvalOneBilinearSubstitution.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffPsiPNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
open MvPolynomial
variable {K : Type} [Field K] {D N : ℕ}
abbrev V (D N : ℕ) : Type := (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)
noncomputable def ev1 : MvPolynomial (V D N) K →ₐ[K] MvPolynomial (V D N) K :=
  aeval fun v => if v = Sum.inr 0 then 1 else X v
noncomputable def thetaS (sgn : K) : MvPolynomial (V D N) K →ₐ[K] MvPolynomial (V D N) K :=
  aeval fun v => match v with
    | Sum.inl (a, j) => if a = 0 then X (Sum.inl (a, j))
        else X (Sum.inl (a, j)) + C sgn * X (Sum.inr a) * X (Sum.inl (0, j))
    | Sum.inr i => X (Sum.inr i)
theorem thetaS_X_inr (sgn : K) (i : Fin (D + 2)) :
    thetaS (D := D) (N := N) sgn (X (Sum.inr i)) = X (Sum.inr i) := by
  simp [thetaS]
theorem thetaS_X_inl_zero (sgn : K) (j : Fin (N + 1)) :
    thetaS (D := D) (N := N) sgn (X (Sum.inl (0, j))) = X (Sum.inl (0, j)) := by
  simp [thetaS]
theorem thetaS_X_inl_of_ne_zero (sgn : K) {a : Fin (D + 2)} (ha : a ≠ 0) (j : Fin (N + 1)) :
    thetaS (D := D) (N := N) sgn (X (Sum.inl (a, j))) =
      X (Sum.inl (a, j)) + C sgn * X (Sum.inr a) * X (Sum.inl (0, j)) := by
  simp [thetaS, ha]
theorem thetaS_comp (s t : K) (hst : s + t = 0) :
    (thetaS (D := D) (N := N) s).comp (thetaS t) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  rintro (⟨a, j⟩ | i)
  · by_cases ha : a = 0
    · subst ha
      simp only [AlgHom.comp_apply, AlgHom.id_apply, thetaS_X_inl_zero]
    · have hC : (C s + C t : MvPolynomial (V D N) K) = 0 := by
        rw [← C_add, hst, C_0]
      simp only [AlgHom.comp_apply, AlgHom.id_apply, thetaS_X_inl_of_ne_zero _ ha, map_add, map_mul,
        thetaS_X_inr, thetaS_X_inl_zero, algHom_C, algebraMap_eq]
      linear_combination
        (X (Sum.inr a) * X (Sum.inl (0, j)) : MvPolynomial (V D N) K) * hC
  · simp only [AlgHom.comp_apply, AlgHom.id_apply, thetaS_X_inr]
noncomputable def theta : MvPolynomial (V D N) K ≃ₐ[K] MvPolynomial (V D N) K :=
  AlgEquiv.ofAlgHom (thetaS (-1)) (thetaS 1) (thetaS_comp _ _ (by ring)) (thetaS_comp _ _ (by ring))
def iota (p : TVar D N) : V D N := Sum.inl (p.1.succ, p.2)
end ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution



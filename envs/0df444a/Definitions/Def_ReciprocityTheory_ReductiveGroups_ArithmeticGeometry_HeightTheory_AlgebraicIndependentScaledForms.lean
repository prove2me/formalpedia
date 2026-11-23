-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentScaledForms
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentScaledForms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:14.762322+00:00
-- url     : https://prove2.me/theorems/3810d6e8-2974-47b8-abe8-9ac60c566351
-- title:
--   Algebraic Independent Scaled Forms
-- statement:
--   Definitions and structural lemmas for Algebraic Independent Scaled Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraicIndependentScaledForms.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsDualDerivations
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_AlgStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
def hupa1Row (D : ℕ) (o : Option (Fin D)) : Fin (D + 2) := Fin.castSucc ((finSuccEquiv D).symm o)
def hupa1Eqv (D N : ℕ) :
    Option ((Fin (D + 2) × Fin (N + 1)) ⊕ Option (Fin D)) ≃ ((Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)) where
  toFun v := match v with
    | none => Sum.inr (Fin.last (D + 1))
    | some (Sum.inl p) => Sum.inl p
    | some (Sum.inr o) => Sum.inr (hupa1Row D o)
  invFun v := match v with
    | Sum.inl p => some (Sum.inl p)
    | Sum.inr i => match finSuccEquivLast i with
      | none => none
      | some t => some (Sum.inr (finSuccEquiv D t))
  left_inv v := by
    rcases v with _ | p | o
    · simp
    · rfl
    · simp [hupa1Row]
  right_inv v := by
    rcases v with p | i
    · rfl
    · dsimp only
      rcases h : finSuccEquivLast i with _ | t
      · have : i = finSuccEquivLast.symm none := (Equiv.eq_symm_apply _).2 h
        simp [this]
      · have : i = finSuccEquivLast.symm (some t) := (Equiv.eq_symm_apply _).2 h
        simp [this, hupa1Row]
end ReciprocityTheory.ChartRestriction.G.T0



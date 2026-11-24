-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_WeilNumbersImpVerticalDivisorsCommute
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_WeilNumbersImpVerticalDivisorsCommute
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:26.427555+00:00
-- url     : https://prove2.me/theorems/82f36b76-2f32-4bd1-9e0d-32727083e6c5
-- title:
--   Weil Numbers Imp Vertical Divisors Commute
-- statement:
--   Definitions and structural lemmas for Weil Numbers Imp Vertical Divisors Commute, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WeilNumbersImpVerticalDivisorsCommute.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsComponentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByFormField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialQuotDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDivCycleSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace VerticalDivisorsCommuting
def CartierStatement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (n : ℕ) (b b' : K → ℤ) (f g f' g' : MRing ι O)
      (L : Fin n → K → ℤ) (Iκ : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily (IsLocalRing.ResidueField O) ι),
      IndefiniteRowSideFullHecke.NumbersDVR.IsModelOver P (n + 1) → IsVerticalDivisor P ϖ b f g →
      IsVerticalDivisor P ϖ b' f' g' → ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection Iκ →
      IndefiniteRowSideFullHecke.NumbersDVR.redEval (fun G => Iκ G (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b'))
                                (IndefiniteRowSideFullHecke.NumbersDVR.divO P f g) =
        IndefiniteRowSideFullHecke.NumbersDVR.redEval (fun G => Iκ G (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b))
          (IndefiniteRowSideFullHecke.NumbersDVR.divO P f' g')
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
end VerticalDivisorsCommuting
end
end GroundTheory.Heights₂.Heights.NumbersDVR



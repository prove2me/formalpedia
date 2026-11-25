-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionKoszul
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionKoszul
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T04:59:23.142309+00:00
-- url     : https://prove2.me/theorems/78feb2fe-87df-5148-b398-b8ff105b33c2
-- title:
--   PPair Number Expansion Koszul
-- statement:
--   Definitions and structural lemmas for PPair Number Expansion Koszul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
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
section Koszul
variable {n : ℕ}
def pairDiff (i : Fin n) : MvPolynomial (Fin n ⊕ Fin n) ℤ := X (Sum.inl i) - X (Sum.inr i)
def pairCollapse (p : Fin n) : Fin n ⊕ Fin n → Fin n ⊕ Fin n :=
  fun s => if s = Sum.inl p then Sum.inr p else s
end Koszul
section Numbers
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
end Numbers
section Additivity
end Additivity
end
end GroundTheory.Heights₂.Heights.NumbersDVR



-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ContractMixed
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ContractMixed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:55.6108+00:00
-- url     : https://prove2.me/theorems/18f7510f-874b-45aa-a874-c19673f41176
-- title:
--   Contract Mixed
-- statement:
--   Definitions and structural lemmas for Contract Mixed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixed.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFIntZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFVert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter
namespace ContractMixed
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
def PrefixPull (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) {n : ℕ} (L' : Fin n → HermLine ι') :
    Prop :=
  ∃ (h : p ≤ n) (L : Fin p → HermLine ι), (∀ j, IsSmoothHerm (L j)) ∧
    ∀ j, IsPullHerm κ v (L j) (L' (Fin.castLE h j))
end ContractMixed
end GroundTheory.Heights₂.Heights.Targets



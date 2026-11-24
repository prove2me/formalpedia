-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingDimOne
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingDimOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:49.107682+00:00
-- url     : https://prove2.me/theorems/0491c577-7e05-418a-8c74-d858d2da11ba
-- title:
--   Statements Loc Ring Dim One
-- statement:
--   Definitions and structural lemmas for Statements Loc Ring Dim One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsLocRingDimOne.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
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
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
def LocRingDimOne.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (s : MRing ι) (a : K → ℕ)
    (W : Ideal (MRing ι)),
    IsMultiProjPrime P → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s →
    IsNoetherianRing (locRing P W) ∧ IsLocalRing (locRing P W) ∧ ringKrullDim (locRing P W) = 1
end GroundTheory.Heights₂.Heights.Inter



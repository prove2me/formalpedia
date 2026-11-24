-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeChart
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:33.682821+00:00
-- url     : https://prove2.me/theorems/75537950-e8f7-404c-87d7-8839f7efe0f3
-- title:
--   Statements Cone Chart
-- statement:
--   Definitions and structural lemmas for Statements Cone Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeChart.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemMinimalPrimesOfMemFundCycleSupport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
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
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj ptsIntegralAt pot)
def ConeIntegralChart.Statement : Prop :=
  ∀ (n e : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (P : Ideal (MRing (PBlk n)))
    (u : Fin n → ℂ) (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → (∀ W ∈ (fundCycle (complexFibreIdeal P)).support, linForm u ∉ W) →
      IsGoodProj P Ψ →
      coneIntegral (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P) e
          (fsLog (ObjectsHeight.ofPointMatrix S hS) u) =
        ptsIntegralAt P Ψ (pot fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
          (IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u)
end GroundTheory.Heights₂.Heights



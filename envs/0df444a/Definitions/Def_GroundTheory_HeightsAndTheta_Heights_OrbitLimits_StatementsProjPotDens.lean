-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotDens
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotDens
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T13:33:47.188971+00:00
-- url     : https://prove2.me/theorems/7c3d6546-f60c-515d-81d4-b0d75a05697f
-- title:
--   Statements Proj Pot Dens
-- statement:
--   Definitions and structural lemmas for Statements Proj Pot Dens, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsProjPotDens.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjFullRankDense
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
def ProjPotDens.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → ∀ j, ∀ y ∈ (BV.chart j).target,
      0 ≤ locDens BV (fun _ => multiprojPot R V) j y ∧
        ((BV.chart j).symm y ∈ projFullRank R BV →
          0 < locDens BV (fun _ => multiprojPot R V) j y)
end GroundTheory.Heights₂.Heights.Targets



-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassPos
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassPos
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T13:27:04.144688+00:00
-- url     : https://prove2.me/theorems/0d34bede-15b1-58cd-88e3-c6d7d44bebce
-- title:
--   Statements Proj Pot Mass Pos
-- statement:
--   Definitions and structural lemmas for Statements Proj Pot Mass Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsProjPotMassPos.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassEq
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
def ProjPotMassPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → IsClosed V →
    ∀ C : Set V, IsOpen C → (C ∩ projFullRank R BV).Nonempty →
      0 < mInt BV (fun _ => multiprojPot R V) (C.indicator fun _ => (1 : ℝ))
end GroundTheory.Heights₂.Heights.Targets



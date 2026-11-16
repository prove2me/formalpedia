-- Prove2me | Definitions.Def_APFPaper5_K1_MovesAtOccupant
-- name    : APFPaper5_K1_MovesAtOccupant
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T19:45:45.422793+00:00
-- url     : https://prove2.me/theorems/eb79057c-b2a5-4acf-ac25-22fc8db30744
-- title:
--   One-opposition motion and opposite-reaching at a selected record
-- statement:
--   Defines MovesOneAwayAt by overlap n minus 2 and ReachesOpposite by a finite iterate equal to the opposite record. These are named K-layer hypotheses, not declared inputs or derived motion. The first is local to v0 and uses a finite distinction type; it is not the older every-record motion condition.
--
--   **Supplied data and hypotheses**
--
--   - These are named K-layer hypotheses, not declared inputs or derived motion. The first is local to v0 and uses a finite distinction type; it is not the older every-record motion condition.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions.Def_APFPaper5_K1_MovesAtOccupant; Sib v66 / pullbacks v22, SHA-256 58d0ba05a0d7760eb7b01e0a7be5478db7f1029d54f06c5bfb4e1194158e32af. rv2_v66_v22_PRIOR_WORK_CHECK.json; rv2_v66_v22_SOURCE_READ_SUPPLEMENT.json; C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-15_session\astra\sib_v66_publication\source\Definitions\Def_APFPaper5_K1_MovesAtOccupant.lean

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFPaper5_K1_MovesAtOccupant
title: "Something moves" as said of the record held: one opposition away at one moment; and "through its whole range": the history reaches the opposite record
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's ruling of 2026-11-14 15:41 HST, "Proceed as advised"
 (RULING_moves_said_of_the_occupant_2026-11-14), on sentence IV of NOTE_derivation_pass_35_2026-11-13; the
 relation sentence adopted on 2026-11-13 10:46 HST ("through its whole range and back"). Paper 5 Supplement
 v7.33:1565-1583 (that a held family moves is a supplied premise there). FOUNDATION_INPUTS is not consumed.
standing: two NAMED HYPOTHESES of the K layer in the ADOPTED READING of 15:41 HST. Neither is a declared input
 and neither is derived. Def_APFPaper5_K1_Moves (MovesOneAway, TwoStepsNotBack: said of every record) is kept
 as the stronger form; it is no longer the reading of sentence IV.
contents: MovesOneAwayAt g v0: the step takes the record v0 exactly one opposition away. ReachesOpposite g
 v0: after some number of steps the record is on the other side of every distinction.
-/
import Definitions.Def_APFPaper5_K1_AlignmentCount
import Definitions.Def_APFPaper5_K1_RegionSymmetries

set_option autoImplicit false
namespace APFPaper5.K1

/-- The step takes the record held exactly one opposition away. -/
def MovesOneAwayAt {D : Type*} [Fintype D] (g : (D → Bool) → D → Bool) (v0 : D → Bool) : Prop :=
  overlapOn Finset.univ v0 (g v0) = ((Finset.univ : Finset D).card : ℝ) - 2

/-- The history of the record held reaches the opposite record. -/
def ReachesOpposite {D : Type*} (g : (D → Bool) → D → Bool) (v0 : D → Bool) : Prop :=
  ∃ m : ℕ, g^[m] v0 = opposite v0

end APFPaper5.K1



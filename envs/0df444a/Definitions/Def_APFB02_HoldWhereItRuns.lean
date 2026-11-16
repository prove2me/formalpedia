-- Prove2me | Definitions.Def_APFB02_HoldWhereItRuns
-- name    : APFB02_HoldWhereItRuns
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T19:45:19.139811+00:00
-- url     : https://prove2.me/theorems/5dffcead-cf5e-41cc-a082-af2dcde4dc34
-- title:
--   Every finite side assignment after a partial move: a named condition
-- statement:
--   StillHeldAfterOn asks for every finite side assignment among images of states where runs holds. The extension of the hold reading to a restricted running domain is a test interpretation, not an installed B02 clause or a theorem that any physical protocol satisfies it.
--
--   **Supplied data and hypotheses**
--
--   - The extension of the hold reading to a restricted running domain is a test interpretation, not an installed B02 clause or a theorem that any physical protocol satisfies it.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions.Def_APFB02_HoldWhereItRuns; Sib v66 / pullbacks v22, SHA-256 43cdce2b39ae2b8a78ce2ad369311363af85898e8e34f27d610e85eb56dd4bf1. rv2_v66_v22_PRIOR_WORK_CHECK.json; rv2_v66_v22_SOURCE_READ_SUPPLEMENT.json; C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-15_session\astra\sib_v66_publication\source\Definitions\Def_APFB02_HoldWhereItRuns.lean

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFB02_HoldWhereItRuns
title: The second hold reading, said of a hold that need not run at every state
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's ruling of 2026-11-14 11:33 HST (RULING_hold_readings_2026-11-14), adopting as a reading
 of a hold: "B02's second sentence is still true of the states the hold leads to". FOUNDATION_INPUTS.json
 revision 2026-11-14.1, B02, second sentence. Def_APFB02_HoldOnDistinctions (StillHeldAfter, typed for a map
 defined at every state). The author, 2026-11-14 17:21 HST: "It sounds like we should be able to derive
 that!".
standing: the SAME ADOPTED READING, typed without assuming that the hold runs at every state. "The states the
 hold leads to" are the states it takes the states where it runs to. Where it runs at every state this is
 StillHeldAfter (APFB02.stillHeldAfterOn_univ_iff). That the adopted words are to be read of the hold as it
 runs, and not of a map that extends it, is this seat's reading of them; if it is not what was meant, this
 header is to be corrected.
statement: StillHeldAfterOn.
-/
import Definitions.Def_APFB02_HoldOnDistinctions

set_option autoImplicit false
namespace APFB02

/-- B02's second sentence said of the states a hold leads to, for a hold that runs where `runs` says:
every combination of sides of every finite family of the distinctions is held by some state the hold
leads to. -/
def StillHeldAfterOn {X D : Type*} (reads : D → X → Bool) (runs : X → Prop) (h : X → X) : Prop :=
  EveryCombinationHeld (fun (d : D) (x : {x : X // runs x}) => reads d (h x.1))

end APFB02



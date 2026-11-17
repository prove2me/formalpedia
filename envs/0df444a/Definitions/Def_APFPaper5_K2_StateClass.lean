-- Prove2me | Definitions.Def_APFPaper5_K2_StateClass
-- name    : APFPaper5_K2_StateClass
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:22:25.930082+00:00
-- url     : https://prove2.me/theorems/f9ab730d-04d2-4007-9433-fd76579b1f72
-- title:
--   Candidate classes of held distinctions and records
-- statement:
--   Active 0/1 and signed-side candidates remain mathematical alternatives; keptClass is the adopted reading for the recorded part only. partyClass, recordForm and markLift are weighted record-space definitions. The unrecorded part is unspecified.
--
--   **Supplied data and hypotheses**
--
--   - Every parameter and hypothesis in the exact source declaration remains exposed; no author input is adopted.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions.Def_APFPaper5_K2_StateClass; Pullbacks v39, SHA-256 0b92addd71027347a462e16e4d2483c4b94b1a093fd8e39cf8c9315e79099b89. Definitions.Def_APFPaper5_K2_StateClass; pullbacks v39; SHA-256 0b92addd71027347a462e16e4d2483c4b94b1a093fd8e39cf8c9315e79099b89

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K2_StateClass
title: What a state holds, as a class. RULED for what is recorded: the records its held family keeps. Two other candidates, not chosen, are kept as typed
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
ruling: the author, 2026-11-15 13:52 HST, "Seems like this is ok as it's about records which are not ever in
 superposition?", and 13:54 HST, "Yes", to this seat's "Shall I record this as your ruling: C for what is
 recorded, records are never in superposition, and the unrecorded part is left to K3?"
 (RULING_C_for_what_is_recorded_2026-11-15).
source: TEE_UP_K2_what_a_state_holds_2026-11-15 (the author, 2026-11-15 13:34 HST: "Yes", to "Shall I tee
 that up?"). Paper 1 Supplement v9.28:1829-1843 (a structural alignment is a carrier and a finite family of
 distinctions each reading 1 on it; "what the substrate is actually holding"), 1852-1860 (its cost: the sum
 of the costs of the carried distinctions plus an interface residue). FOUNDATION_INPUTS revision
 2026-11-14.1, B02, second sentence (every combination of sides is held). The builder seat's
 Def_APFPaper5_K1_MarkTable (ind, atomTable, tableForm) and Def_APFPaper5_K1_PartyScore (keptCost).
standing: keptClass, partyClass, recordForm and markLift carry the ruling: for what is RECORDED, the class of
 a held family is the list of records it keeps. activeClass (A) and sideClass (B) were NOT chosen; they are
 kept so that Thm_APFPaper5_K2_state_class_candidates still states what each costs. Nothing here is an
 input. What a state holds that is not recorded is not typed; it is left to K3.
definitions:
 - activeClass (candidate A, not chosen): on each listed distinction, 1 if the state reads it true and 0 if not.
 - sideClass (candidate B, not chosen): on each listed distinction, 1 if the state reads it true and -1 if not.
 - keptClass (C, ruled for what is recorded): on each record, 1 if the family keeps it and 0 if not. A class of records, not of
   distinctions.
 - partyClass: on each record, 1 if the distinction is listed against it and 0 if not.
 - recordForm: the weighted overlap of two classes of records.
 - markLift: the class of records a class of distinctions stands for: each distinction's list, added up.
no structure, no class, no Prop-valued field.
-/
import Definitions.Def_APFPaper5_K1_MarkTable
import Definitions.Def_APFPaper5_K1_PartyScore

set_option autoImplicit false
open APFPaper5.K1

namespace APFPaper5.K2

universe uI uX uD uW
variable {ι : Type uI} {X : Type uX} {D : Type uD} {W : Type uW}

/-- Candidate A (not chosen): the distinctions that read true, added up. -/
def activeClass (reads : D → X → Bool) (dist : ι → D) (x : X) : ι → ℝ :=
  fun i => ind (reads (dist i) x)

/-- Candidate B (not chosen): the side of each listed distinction. -/
def sideClass (reads : D → X → Bool) (dist : ι → D) (x : X) : ι → ℝ :=
  fun i => if reads (dist i) x then 1 else -1

/-- C, ruled for what is recorded: the records a family keeps, as a class of records. -/
def keptClass (keeps : Finset D → W → Bool) (S : Finset D) : W → ℝ :=
  fun a => ind (keeps S a)

/-- The records a distinction is listed against, as a class of records. -/
def partyClass (mark : ι → W → Bool) (i : ι) : W → ℝ :=
  fun a => ind (mark i a)

/-- The weighted overlap of two classes of records. -/
def recordForm [Fintype W] (w : W → ℝ) (u v : W → ℝ) : ℝ :=
  ∑ a, w a * (u a * v a)

/-- The class of records a class of distinctions stands for. -/
def markLift [Fintype ι] (mark : ι → W → Bool) (x : ι → ℝ) : W → ℝ :=
  fun a => ∑ i, x i * ind (mark i a)

end APFPaper5.K2



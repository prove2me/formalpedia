-- Prove2me | Definitions.Def_APFPaper5_K1_PartyScore
-- name    : APFPaper5_K1_PartyScore
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:20:21.293279+00:00
-- url     : https://prove2.me/theorems/ee6ec9f0-bc7d-4d44-a99d-85a23cbdb4a4
-- title:
--   Party-to records and their weighted score
-- statement:
--   A distinction is party to a record when adding it changes some finite family's keeping decision. The score sums weights of records to which both distinctions are party. Shared and joint keeping rules are supplied definitions.
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
--   Definitions.Def_APFPaper5_K1_PartyScore; Pullbacks v39, SHA-256 aba7527cbdcceafb4aff1832e001ba1b51d32b1879e31f62492664d8e1d71e03. Definitions.Def_APFPaper5_K1_PartyScore; pullbacks v39; SHA-256 aba7527cbdcceafb4aff1832e001ba1b51d32b1879e31f62492664d8e1d71e03

/-
RE-HEADED 2026-11-15 05:21 HST by the seat that wrote this file. Only this block is new. The original
header below it and all code are unchanged. Where the original header differs from this block, this block
governs. Pre-edit copy: bundle v28 (sha256 a6e8f608...29d0017) and Old/ in the working tree.
 - "PARTY TO" IS CONFIRMED. The author, 2026-11-15 05:07 HST: "1 Confirmed, please proceed", item 1 of
   this seat's list of 05:00 HST being "Confirm my typing of 'party to': adding the distinction to some
   family makes the record kept." RULING_party_to_confirmed_2026-11-15. So the line below that calls
   PartyTo "NOT RULED" is OUT OF DATE.
 - The ledger form of this score is in Def_APFPaper5_K1_LedgerPartyScore (pass 40).
 - Unchanged: no lane; no claim that the transfer is forced, that the carrier gap is closed or narrowed, or
   that Born is derived.
---- original header (pass 39, 2026-11-14 22:13 HST onward) follows ----
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_PartyScore
title: On a keeping rule: a distinction is party to a record when adding it to some family makes the record kept; the score of two distinctions is the total cost of the records both are party to
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 22:13 HST: "B", in answer to TEE_UP_K1_score_with_joint_records_2026-11-14.
 Option B there reads: "the score of two distinctions is the cost of the records both are party to, a joint
 record counted like a shared one." RULING_K1_score_with_joint_records_2026-11-14.
standing:
 - partyScore: a DEFINITION, the typed form of the author's ruling B. A choice of a score from a keeping
   rule and record costs. Where a joint record is present it REPLACES the shared cost as the ledger form of
   K1's score (call 1 of 19:57 HST, narrowed by B). With no joint record the two agree
   (Thm_APFPaper5_K1_party_score).
 - PartyTo: THIS SEAT'S TYPING of the words "party to". NOT RULED. The tee-up named it as a new word.
   It is defined from the keeping rule alone and adds no primitive.
 - keepsB, keptCost: the keeping rule and cost of a book with two kinds of record, the object the ruling
   is said of. A definition; nothing is asserted to exist.
what it rules out: reading K1's score off costs alone. Two books with the same costs can have different
 scores (TEE_UP fact 9, not typed in general). It also sets aside the variant that leaves joint records
 out of the table, which the author did not choose.
what this file does NOT say: that any world has such a book; that the role exchange is anything but the
 identity; anything about orientation or K3. FOUNDATION_INPUTS is unchanged and nothing here is installed.
 No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
 is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_MarkTable
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

set_option autoImplicit false

namespace APFPaper5.K1

universe u v
variable {D : Type u} {W : Type v}

/-- A distinction is party to a record when adding it to some family makes the record kept. -/
def PartyTo [DecidableEq D] (keeps : Finset D → W → Bool) (d : D) (a : W) : Prop :=
  ∃ S : Finset D, keeps (insert d S) a = true ∧ keeps S a = false

/-- `PartyTo` as a mark, for use in a record-book table. -/
noncomputable def partyMark [DecidableEq D] (keeps : Finset D → W → Bool) (d : D) (a : W) : Bool :=
  @decide (PartyTo keeps d a) (Classical.propDecidable _)

/-- The cost of a family: the total cost of the records it keeps. -/
noncomputable def keptCost [Fintype W] (w : W → ℝ) (keeps : Finset D → W → Bool) (S : Finset D) : ℝ :=
  ∑ a, w a * ind (keeps S a)

/-- The score of two distinctions: the total cost of the records both are party to. -/
noncomputable def partyScore [Fintype D] [DecidableEq D] [Fintype W] (w : W → ℝ)
    (keeps : Finset D → W → Bool) (i j : D) : ℝ :=
  atomTable w (partyMark keeps) i j

/-- The keeping rule of a book with two kinds of record. `mark d a` says the book lists `d` against `a`.
A shared record is kept when some listed distinction is held; a joint record when every one is. -/
def keepsB [Fintype D] [DecidableEq D] (mark : D → W → Bool) (joint : W → Bool) (S : Finset D) (a : W) :
    Bool :=
  if joint a = true then decide (∀ i, mark i a = true → i ∈ S) else decide (∃ i ∈ S, mark i a = true)

end APFPaper5.K1



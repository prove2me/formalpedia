-- Prove2me | Definitions.Def_APFPaper5_K1_LedgerPartyScore
-- name    : APFPaper5_K1_LedgerPartyScore
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:21:25.035027+00:00
-- url     : https://prove2.me/theorems/93dd57d3-00e4-4e0d-ac20-fa19cf082466
-- title:
--   Party score on a supplied record ledger
-- statement:
--   Serving, universally needed records, the induced keeping rule and its weighted party score are defined on a RecordLedger. A universally quantified need can be vacuous when no protocol serves the family; feasibility remains explicit where required.
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
--   Definitions.Def_APFPaper5_K1_LedgerPartyScore; Pullbacks v39, SHA-256 ea201ba0aeff8efcfd0123bc6b64c7f19be7474e4767010dfb200597c902dcbe. Definitions.Def_APFPaper5_K1_LedgerPartyScore; pullbacks v39; SHA-256 ea201ba0aeff8efcfd0123bc6b64c7f19be7474e4767010dfb200597c902dcbe

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_LedgerPartyScore
title: On a record ledger: the records a family needs are those every protocol serving it keeps; the ledger form of K1's score for two members of an indexed family is the total cost of the records both are party to
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 22:13 HST: "B" (RULING_K1_score_with_joint_records_2026-11-14); and
 2026-11-15 05:07 HST: "1 Confirmed, please proceed" (RULING_party_to_confirmed_2026-11-15), confirming
 "party to" as typed in Def_APFPaper5_K1_PartyScore. Record ledger: Def_APFPaper1_RecordLedger (pass 28).
standing:
 - Serves, familyNeeds: DEFINITIONS in the declared vocabulary. Serves is the serving clause of the
   declared family cost, word for word, on the ledger's data. familyNeeds adds no primitive.
 - ledgerKeeps, ledgerPartyScore: the keeping rule and the score of ruling B, on a record ledger. A
   DEFINITION, adopted by the author's ruling B with "party to" as he confirmed it.
 - The record ledger itself is NOT installed. The author, 2026-11-14 20:26 HST: "The record ledger can be
   derived - each item in it". These definitions sit on it as it was typed in pass 28.
what it rules out: reading the score off family costs alone. The score reads which records each family
 needs and what each record costs.
what this file does NOT say: that any ledger exists; that family needs are the union of the members'
 needs (they are where the availability sentence holds, and need not be otherwise: that difference is what
 a joint record is here). No lane. No claim that the transfer is forced, that the carrier gap is closed or
 narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_PartyScore
import Definitions.Def_APFPaper1_RecordLedger
import Mathlib.Data.Finset.Image

set_option autoImplicit false

open APFPaper1

namespace APFPaper5.K1

variable {D P Record : Type*}

/-- A protocol serves a family: for each member it keeps a set of records sufficient for it and uses it.
The serving clause of the declared family cost, on the ledger's data. -/
def Serves (L : RecordLedger D P Record) (p : P) (S : Finset D) : Prop :=
  ∀ d ∈ S, ∃ sigma : Set Record,
    sigma ⊆ L.maintained p ∧ L.sufficient p sigma d ∧ L.usesToRealize p d sigma

/-- The records a family needs: those that every protocol serving the family keeps. -/
def familyNeeds (L : RecordLedger D P Record) (S : Finset D) : Set Record :=
  {a | ∀ p : P, Serves L p S → a ∈ L.kept p}

/-- The ledger's keeping rule on an indexed family: a record is kept by a set of indices when the family
of their distinctions needs it. -/
noncomputable def ledgerKeeps {ι : Type*} [DecidableEq D] (L : RecordLedger D P Record) (dist : ι → D)
    (S : Finset ι) (a : Record) : Bool :=
  @decide (a ∈ familyNeeds L (S.image dist)) (Classical.propDecidable _)

/-- The ledger form of K1's score (ruling B): the total cost of the records both are party to. -/
noncomputable def ledgerPartyScore {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]
    [Fintype Record] (L : RecordLedger D P Record) (dist : ι → D) (i j : ι) : ℝ :=
  partyScore (fun a => ((L.cost a : NNReal) : ℝ)) (ledgerKeeps L dist) i j

end APFPaper5.K1



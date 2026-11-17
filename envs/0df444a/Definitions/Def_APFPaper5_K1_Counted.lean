-- Prove2me | Definitions.Def_APFPaper5_K1_Counted
-- name    : APFPaper5_K1_Counted
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:22:33.283758+00:00
-- url     : https://prove2.me/theorems/2cffd115-a039-479d-8ad9-6b1eee4c56a0
-- title:
--   Counted families with an own paid record
-- statement:
--   Counted combines the earlier LedgerCounted predicate with a strictly positive record needed by each member alone and not by the remaining family. This is a definition on a supplied record ledger; existence is not asserted.
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
--   Definitions.Def_APFPaper5_K1_Counted; Pullbacks v39, SHA-256 ad50bddde4b83407f79691ce1aae17ec3eae2d5d96143a5aa13e70b1a51434b9. Definitions.Def_APFPaper5_K1_Counted; pullbacks v39; SHA-256 ad50bddde4b83407f79691ce1aae17ec3eae2d5d96143a5aa13e70b1a51434b9

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_Counted
title: On a record ledger, a counted family: within capacity, each member tested and support-novel over the others, and each member, held alone, needing a record of positive cost that the others together do not need
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-15 06:17 HST: "A", in answer to TEE_UP_counted_own_record_2026-11-15. Option A
 there: the clause "held alone, each counted distinction needs a record of positive cost that the others
 together do not need" is part of what "counted" means. RULING_counted_includes_own_record_2026-11-15.
 Before it: the author's call 2 of 2026-11-14 19:57 HST (a finite family within capacity, each member
 tested and support-novel over the others), typed as LedgerCounted in Def_APFPaper5_K1_LedgerScore.
standing:
 - Counted: a DEFINITION, the typed form of what "counted" means from 2026-11-15 06:17 HST. It is call 2
   as first typed (LedgerCounted) together with the own-record clause (HasOwnPaidRecord).
 - It asserts that nothing exists. It adds no input. It sits on the record ledger of pass 28, which is
   NOT installed (the author, 2026-11-14 20:26 HST).
what it rules out: families in which some member has no record of its own that costs something. Two are
 typed: the free pair and the twins (Thm_APFPaper5_K1_counted_family, not_counted).
what this file does NOT say:
 - That the clause is needed for K1. It is sufficient and stronger than K1 needs
   (partyScore_faithful_iff has the exact condition).
 - That a region's distinctions are counted. Where the availability sentence holds that follows from the
   declared B05 (counted_of_available). Where a joint record is present it has to be shown.
 - It is not the singleton floor MD of Paper 1's Supplement: it puts no floor on every distinction.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_LedgerScore
import Definitions.Def_APFPaper5_K1_LedgerPartyScore

set_option autoImplicit false

open APFPaper1 APFPaper1.Source

namespace APFPaper5.K1

variable {D P Record : Type*}

/-- The own-record clause: held alone, each member needs a record of positive cost that the others
together do not need. -/
def HasOwnPaidRecord {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]
    (L : RecordLedger D P Record) (dist : ι → D) : Prop :=
  ∀ i, ∃ a, 0 < L.cost a ∧ a ∈ familyNeeds L {dist i} ∧
    a ∉ familyNeeds L ((Finset.univ.erase i).image dist)

/-- A counted family: within capacity, each member tested and support-novel over the others, and each
with a record of its own that costs something. -/
def Counted {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]
    (L : RecordLedger D P Record) (tested : D → Prop) (C : ℝ) (dist : ι → D) : Prop :=
  LedgerCounted L tested C dist ∧ HasOwnPaidRecord L dist

end APFPaper5.K1



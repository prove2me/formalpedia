-- Prove2me | Definitions.Def_APFPaper5_K1_SourcePartyScore
-- name    : APFPaper5_K1_SourcePartyScore
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:21:25.324214+00:00
-- url     : https://prove2.me/theorems/5c390411-a9f1-4437-b9c2-a8843c4f51df
-- title:
--   Party score and countedness on source data
-- statement:
--   The definitions use supplied protocols, maintained records, sufficient support and use predicates. SourceCounted includes the own paid record clause. leastBill is an unruled candidate: the real infimum of bills maintaining a record, with empty infimum zero, not the paper's extended-real infinity convention.
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
--   Definitions.Def_APFPaper5_K1_SourcePartyScore; Pullbacks v39, SHA-256 a270c067117d18605b6244c88b71b3763a0766d3f77399fc61b10c063c080345. Definitions.Def_APFPaper5_K1_SourcePartyScore; pullbacks v39; SHA-256 a270c067117d18605b6244c88b71b3763a0766d3f77399fc61b10c063c080345

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_SourcePartyScore
title: On source data of the declared forms: the records a family needs, K1's score for a given cost of each record, a counted family, and the least bill as one cost every record carries
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-15 06:55 HST: "1", in answer to this seat's "1. Derive the record ledger item by
 item from the eight." And 07:00 HST: "Would like the goal here to be adding the work to our p2m
 foundation… thinking it would be ideal to bolt on the Ks to that model? The goal is a P2m that takes us
 from first principals to quantum and gauge form". Read as: state the K layer on the foundation's own
 data. RULING_ledger_item_by_item_and_the_goal_2026-11-15.
 Carried over unchanged from the record ledger: ruling B (2026-11-14 22:13 HST, the score), "party to"
 (2026-11-15 05:07 HST), call 2 and ruling A (2026-11-14 19:57 and 2026-11-15 06:17 HST, "counted").
 Paper 1 Supplement v9.28:2197-2221 (a protocol carries a resource load, a calibration values it, and the
 cost of a distinction is the least calibrated load of a protocol realizing it) and 1787-1788 (the cost of
 a family is the least bill of a joint protocol).
standing:
 - SourceServes, sourceNeeds, sourceKeeps: DEFINITIONS in the vocabulary of the declared forms and nothing
   else. SourceServes is the serving clause of the declared family cost, word for word. On a record ledger
   they are the ledger's own (familyNeeds_eq_sourceNeeds holds by definition).
 - sourcePartyScore: the author's ruling B, typed for any cost of records. Not a new ruling.
 - SourceCounted: the author's call 2 and ruling A, typed for any cost of records. Not a new ruling.
 - leastBill: NEW AND NOT RULED. One way to say what a record costs from the source data alone: the least
   bill among the protocols that maintain it. It has the form of the declared cost of a distinction.
   Whether it is what "the cost of a record" means is the author's call.
what leastBill is and is not:
 - It is never negative. A record that no protocol maintains gets zero, by the convention of the infimum
   in the reals; the Supplement's convention at 1788 gives plus infinity for an empty class.
 - On a record ledger it is at least the ledger's cost of a record some protocol keeps, and equal to it
   when some protocol keeps the record alone (cost_le_leastBill, leastBill_eq_cost_of_kept_alone). Where a
   record cannot be kept alone, its least bill includes the cost of its company.
 - It assumes no law on a bill: not that a bill is a sum over records, and not that two protocols keeping
   the same records bill the same.
what this file does NOT say: that any family is counted; that the least bill is the cost of a record in the
 sense of any paper; anything about orientation or the role exchange. Definitions only; nothing is asserted
 to exist. No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or
 that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_PartyScore
import Definitions.Def_APFPaper1_FamilyCost
import Mathlib.Data.Finset.Image

set_option autoImplicit false

open APFPaper1.Source

namespace APFPaper5.K1

variable {D P R Record : Type*}

/-- A protocol serves a family: for each member it maintains a set of records sufficient for it and uses
it. This is the serving clause of the declared family cost, word for word. -/
def SourceServes (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (p : P) (S : Finset D) : Prop :=
  ∀ d ∈ S, ∃ sigma : Set Record,
    sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma

/-- The records a family needs: those that every protocol serving the family maintains. -/
def sourceNeeds (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S : Finset D) : Set Record :=
  {a | ∀ p : P, SourceServes maintained sufficient usesToRealize p S → a ∈ maintained p}

/-- The keeping rule of the source data on an indexed family: a record is kept by a set of indices when
the family of their distinctions needs it. -/
noncomputable def sourceKeeps {ι : Type*} [DecidableEq D] (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (dist : ι → D) (S : Finset ι) (a : Record) : Bool :=
  @decide (a ∈ sourceNeeds maintained sufficient usesToRealize (S.image dist))
    (Classical.propDecidable _)

/-- K1's score on source data (ruling B), for a given cost of each record: the total cost of the records
both distinctions are party to. -/
noncomputable def sourcePartyScore {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]
    [Fintype Record] (w : Record → ℝ) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (dist : ι → D) (i j : ι) : ℝ :=
  partyScore w (sourceKeeps maintained sufficient usesToRealize dist) i j

/-- One cost a record carries on any source data: the least bill among the protocols that maintain it
(the infimum; zero when no protocol maintains it). -/
noncomputable def leastBill (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record) (a : Record) : ℝ :=
  sInf {c : ℝ | ∃ p : P, a ∈ maintained p ∧ (calibration (wholeResource p) : ℝ) = c}

/-- The own-record clause on source data, for a given cost of each record: held alone, each member needs
a record of positive cost that the others together do not need. -/
def SourceHasOwnPaidRecord {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D] (w : Record → ℝ)
    (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (dist : ι → D) : Prop :=
  ∀ i, ∃ a, 0 < w a ∧ a ∈ sourceNeeds maintained sufficient usesToRealize {dist i} ∧
    a ∉ sourceNeeds maintained sufficient usesToRealize ((Finset.univ.erase i).image dist)

/-- A counted family on source data, for a given cost of each record: within capacity, each member tested
and support-novel over the others, and each with a record of its own that costs something. -/
def SourceCounted {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D] (w : Record → ℝ)
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (tested : D → Prop) (C : ℝ) (dist : ι → D) : Prop :=
  (familyAdmissible wholeResource calibration maintained sufficient usesToRealize C
        (Finset.univ.image dist) ∧
      (∀ i, tested (dist i)) ∧
      ∀ i, supportNovel wholeResource calibration maintained sufficient usesToRealize
        ((Finset.univ.erase i).image dist) (dist i)) ∧
    SourceHasOwnPaidRecord w maintained sufficient usesToRealize dist

end APFPaper5.K1



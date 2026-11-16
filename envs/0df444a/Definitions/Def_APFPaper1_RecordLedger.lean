-- Prove2me | Definitions.Def_APFPaper1_RecordLedger
-- name    : APFPaper1_RecordLedger
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T19:45:54.259741+00:00
-- url     : https://prove2.me/theorems/5217b7d2-c6db-48ad-8c5a-06fe706a78d9
-- title:
--   A restricted additive record-ledger representation
-- statement:
--   Defines nonnegative record costs, finite kept sets, sufficiency and use predicates; derives resource/calibration/maintained objects and defines needs as records in every sufficient set. needsFin is empty if needs is not finite. No law-valued field is stored, but the representation narrows bills to sums over kept records. Equal kept sets have equal bills and an empty kept set has zero bill by construction. It does not follow that arbitrary source data admit this representation; no Foundation input is rebound. Needs being necessary does not make them sufficient; existence is not promised.
--
--   **Supplied data and hypotheses**
--
--   - No law-valued field is stored, but the representation narrows bills to sums over kept records. Equal kept sets have equal bills and an empty kept set has zero bill by construction. It does not follow that arbitrary source data admit this representation; no Foundation input is rebound. Needs being necessary does not make them sufficient; existence is not promised.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions.Def_APFPaper1_RecordLedger; Sib v66 / pullbacks v22, SHA-256 9f87bf3d862ae7e859ee5161cb003d6a75f069351de6a419508a317fdbef3c44. rv2_v66_v22_PRIOR_WORK_CHECK.json; rv2_v66_v22_SOURCE_READ_SUPPLEMENT.json; C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-15_session\astra\sib_v66_publication\source\Definitions\Def_APFPaper1_RecordLedger.lean

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper1_RecordLedger
title: A record ledger: records each carry a cost, a protocol keeps a finite set of them, its bill is the sum of their costs, and the records a distinction needs are those every sufficient set contains
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 HST. 20:02: "Second shelf with strong guards must be an option of last
 resort. But definitions are going to be needed." 20:09: "I'm leaning definitions - seems less prone to
 drift?" then "Go" (to: type the ledger and needs, sufficiency first, restate the bridge over them, and
 build the world for the third guard). RULING_K1_tie_in_calls_1_to_4_2026-11-14 (call 3: the bill is a sum
 over finitely many records kept). RULING_K1_tie_in_call_5_2026-11-14.
standing: A DEFINITION, on the definitions route the author chose at 20:09 HST. The structure has data
 fields only and no law field. Everything said of it holds by construction. NOT INSTALLED: the line in
 FOUNDATION_INPUTS naming this as what the eight are read over is the author's to write, and until it is
 written no declared input is read over this definition.
WHAT THIS DEFINITION NARROWS (guard 3). On source data in general a bill is any function of a protocol.
 Here it is the sum of the costs of the records kept. So a record ledger rules out: two protocols that
 keep the same records and bill differently; a protocol that keeps nothing and bills something
 (Thm_APFPaper1_RecordLedger_laws: bill_eq_of_kept_eq, bill_zero_of_kept_empty). The eight declared forms
 put no law on bills and so do not exclude either. A world meeting all eight forms in which the bill is
 not a sum is OWED and is not on file: every world on file that meets the eight is a record ledger.
what it does NOT assert (guard 1): that any protocol, record or distinction exists; that every family
 within capacity has a protocol keeping exactly what it needs (that is the availability sentence, to be an
 input line by the author's ruling on call 4); that having its needs is enough to serve a distinction.
needs, sufficiency first: `needs d` is defined from `sufficient`, not the other way round. So "serving a
 distinction needs that distinction's own records" holds by construction and nothing further is adopted.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper1_FamilyCost
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Basic

set_option autoImplicit false

namespace APFPaper1

/-- A record ledger. Data only: no law is assumed of it. -/
structure RecordLedger (D P Record : Type*) where
  /-- What each record costs. -/
  cost : Record → NNReal
  /-- The finite set of records a protocol keeps. -/
  kept : P → Finset Record
  /-- Which sets of records are sufficient, in a protocol, for a distinction. -/
  sufficient : P → Set Record → D → Prop
  /-- Which sets of records a protocol uses to realize a distinction. -/
  usesToRealize : P → D → Set Record → Prop

namespace RecordLedger

variable {D P Record : Type*} (L : RecordLedger D P Record)

/-- The whole resource of a protocol is the set of records it keeps. -/
def wholeResource : P → Finset Record := L.kept

/-- The bill of a set of records is the sum of their costs. -/
noncomputable def calibration : Finset Record → NNReal := fun r => ∑ a ∈ r, L.cost a

/-- What a protocol maintains is what it keeps. -/
def maintained : P → Set Record := fun p => (↑(L.kept p) : Set Record)

/-- The ledger's family cost: the declared family cost, on the ledger's own data. -/
noncomputable def familyCost : Finset D → ℝ :=
  APFPaper1.Source.familyCost L.wholeResource L.calibration L.maintained L.sufficient L.usesToRealize

/-- The records a distinction needs: those that every sufficient set of records contains. -/
def needs (d : D) : Set Record :=
  {a | ∀ (p : P) (sigma : Set Record), L.sufficient p sigma d → a ∈ sigma}

open Classical in
/-- The needs of a distinction as a finite set, where they are finite; empty otherwise. -/
noncomputable def needsFin (d : D) : Finset Record :=
  if h : (L.needs d).Finite then h.toFinset else ∅

end RecordLedger

end APFPaper1



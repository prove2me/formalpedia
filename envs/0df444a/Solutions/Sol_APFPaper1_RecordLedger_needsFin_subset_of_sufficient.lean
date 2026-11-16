-- Prove2me | solution 1 for APFPaper1.RecordLedger.needsFin_subset_of_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:20:06.950207+00:00
-- url     : https://prove2.me/submissions/9b0cda42-669a-4edb-9f48-93d9d8deb560

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper1_RecordLedger_laws
title: In a record ledger the bill is the sum of the costs of the records kept, what is maintained is what is kept, and serving a distinction takes the records it needs, all by construction; two protocols keeping the same records bill the same, and one keeping nothing bills nothing
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFPaper1_RecordLedger (this seat; the author's "Go" of 2026-11-14 20:09 HST).
standing: THEOREMS OF A DEFINITION. No hypothesis beyond the ledger itself, except where a theorem names a
 protocol that serves the distinction.
what this file says:
 - bill_eq_sum, maintained_eq_kept, needs_subset_of_sufficient, needsFin_subset_of_sufficient: the three
   sentences that were hypotheses of the K1 bridge (the bill is a sum; what is maintained is a finite set
   of records; serving a distinction needs its own records) hold in every record ledger.
 - needs_finite_of_served, coe_needsFin_of_served: where some protocol serves a distinction, its needs are
   finitely many and the finite set is exactly its needs.
 - bill_eq_of_kept_eq, bill_zero_of_kept_empty: what the definition rules out (guard 3).
what this file does NOT say: that the needs of a distinction are sufficient for it; that any protocol
 serves anything. No lane. No claim that the transfer is forced, that the carrier gap is closed or
 narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper1_RecordLedger
import Mathlib.Data.NNReal.Basic

set_option autoImplicit false

namespace APFPaper1.RecordLedger

variable {D P Record : Type*} (L : RecordLedger D P Record)

/-- The bill of a protocol is the sum of the costs of the records it keeps. -/
theorem bill_eq_sum (p : P) :
    ((L.calibration (L.wholeResource p) : NNReal) : ℝ) = ∑ r ∈ L.kept p, ((L.cost r : NNReal) : ℝ) :=
  NNReal.coe_sum _ _

/-- What a protocol maintains is the finite set of records it keeps. -/
theorem maintained_eq_kept (p : P) : L.maintained p = (↑(L.kept p) : Set Record) := rfl

/-- Every sufficient set of records for a distinction contains the records it needs. -/
theorem needs_subset_of_sufficient (p : P) (sigma : Set Record) (d : D)
    (h : L.sufficient p sigma d) : L.needs d ⊆ sigma :=
  fun _ ha => ha p sigma h

/-- The same, for the finite form of the needs. It holds for every distinction. -/
theorem needsFin_subset_of_sufficient (p : P) (sigma : Set Record) (d : D)
    (h : L.sufficient p sigma d) : (↑(L.needsFin d) : Set Record) ⊆ sigma := by
  unfold needsFin
  split_ifs with hfin
  · intro a ha
    have ha' : a ∈ L.needs d := by simpa using ha
    exact ha' p sigma h
  · simp

/-- Where some protocol serves a distinction from records it keeps, the distinction's needs are finitely
many. -/
theorem needs_finite_of_served (d : D) (p : P) (sigma : Set Record) (hsub : sigma ⊆ L.maintained p)
    (h : L.sufficient p sigma d) : (L.needs d).Finite :=
  (Finset.finite_toSet (L.kept p)).subset
    (fun _ ha => hsub (L.needs_subset_of_sufficient p sigma d h ha))

/-- Where some protocol serves a distinction, the finite form is exactly its needs. -/
theorem coe_needsFin_of_served (d : D) (p : P) (sigma : Set Record) (hsub : sigma ⊆ L.maintained p)
    (h : L.sufficient p sigma d) : (↑(L.needsFin d) : Set Record) = L.needs d := by
  have hfin := L.needs_finite_of_served d p sigma hsub h
  unfold needsFin
  rw [dif_pos hfin]
  exact hfin.coe_toFinset

/-- Ruled out by the definition: two protocols that keep the same records bill the same. -/
theorem bill_eq_of_kept_eq (p q : P) (h : L.kept p = L.kept q) :
    L.calibration (L.wholeResource p) = L.calibration (L.wholeResource q) := by
  unfold wholeResource
  rw [h]

/-- Ruled out by the definition: a protocol that keeps nothing bills nothing. -/
theorem bill_zero_of_kept_empty (p : P) (h : L.kept p = ∅) :
    L.calibration (L.wholeResource p) = 0 := by
  unfold wholeResource calibration
  rw [h]
  exact Finset.sum_empty

end APFPaper1.RecordLedger


universe apfNative_u_1 apfNative_u_2 apfNative_u_3
theorem solution :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_3}
  (L : APFPaper1.RecordLedger.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record) (p : P)
  (sigma : Set.{apfNative_u_3} Record) (d : D)
  (h : @APFPaper1.RecordLedger.sufficient.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L p sigma d),
  @LE.le.{apfNative_u_3} (Set.{apfNative_u_3} Record) (@Set.instLE.{apfNative_u_3} Record)
    (@SetLike.coe.{apfNative_u_3, apfNative_u_3} (Finset.{apfNative_u_3} Record) Record
      (@Finset.instSetLike.{apfNative_u_3} Record)
      (@APFPaper1.RecordLedger.needsFin.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L d))
    sigma := by
  exact @APFPaper1.RecordLedger.needsFin_subset_of_sufficient

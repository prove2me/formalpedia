-- Prove2me | solution 1 for APFPaper1.RecordOccupant.turn_invariant_record_speaks_of_pair_relations
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:42:28.964467+00:00
-- url     : https://prove2.me/submissions/febb6606-de97-4c85-b703-e6cb5ca29e7a

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper1_RecordOccupant_turn_invariant_records
title: A record that turning every side over leaves unchanged speaks only of the relations between pairs: two states with the same pair relations are allowed or refused together
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 HST. 21:06: "Yes" (the by-levels reading). 21:11: "Draft candidates" (for the
 rule saying what counts as a unit). TEE_UP_unit_rule_2026-11-14, candidate B. This seat, passes 20 and 25
 (moves that no kept record sees), pass 31 (the parity record, which a turn of every side breaks).
standing: A THEOREM about two-sided marks. No input is consumed. It supports candidate B of the tee-up
 sheet; it does not adopt it.
what this file says: let P be any record on finitely or infinitely many two-sided marks. If P is unchanged
 when every side is turned over, then whether a state is allowed by P depends only on which pairs of marks
 are on the same side.
what this file does NOT say: that every record is unchanged by such a turn (the parity record of pass 31
 is not); anything about marks with more than two sides, a continuum or a carrier; that the eight force
 records to be of this kind. No lane. No claim that the transfer is forced, that the carrier gap is closed
 or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Mathlib.Logic.Basic
import Mathlib.Logic.Nonempty

set_option autoImplicit false

namespace APFPaper1.RecordOccupant

/-- A record unchanged by turning every side over speaks only of the pair relations. -/
theorem turn_invariant_record_speaks_of_pair_relations {ι : Type*} (P : (ι → Bool) → Prop)
    (hinv : ∀ x : ι → Bool, P x → P (fun i => !x i))
    (x y : ι → Bool) (hrel : ∀ i j : ι, (x i = x j) ↔ (y i = y j)) (hx : P x) : P y := by
  by_cases hne : Nonempty ι
  · obtain ⟨i0⟩ := hne
    by_cases h0 : x i0 = y i0
    · have hxy : x = y := by
        funext j
        have hj := hrel i0 j
        cases hx0 : x i0 <;> cases hxj : x j <;> cases hy0 : y i0 <;> cases hyj : y j <;> simp_all
      rw [← hxy]
      exact hx
    · have hxy : y = fun i => !x i := by
        funext j
        have hj := hrel i0 j
        cases hx0 : x i0 <;> cases hxj : x j <;> cases hy0 : y i0 <;> cases hyj : y j <;> simp_all
      rw [hxy]
      exact hinv x hx
  · have hxy : x = y := by
      funext j
      exact absurd ⟨j⟩ hne
    rw [← hxy]
    exact hx

end APFPaper1.RecordOccupant


universe apfNative_u_1
theorem solution :
∀ {ι : Type apfNative_u_1} (P : (ι → Bool) → Prop) (hinv : ∀ (x : ι → Bool), P x → P fun (i : ι) => Bool.not (x i))
  (x y : ι → Bool) (hrel : ∀ (i j : ι), Iff (@Eq.{1} Bool (x i) (x j)) (@Eq.{1} Bool (y i) (y j))) (hx : P x), P y := by
  exact @APFPaper1.RecordOccupant.turn_invariant_record_speaks_of_pair_relations

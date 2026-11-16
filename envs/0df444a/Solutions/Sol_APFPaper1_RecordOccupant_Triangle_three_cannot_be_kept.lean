-- Prove2me | solution 1 for APFPaper1.RecordOccupant.Triangle.three_cannot_be_kept
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T20:12:22.480954+00:00
-- url     : https://prove2.me/submissions/0be1ecc6-79ed-4c22-aba5-564b688898a0

import Definitions.Def_APFPaper1_RecordOccupant_sections_and_free_moves_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper1_RecordOccupant_sections_and_free_moves
title: A move that no kept record sees and that flips a distinction leaves the occupant in raw form on it; record sets that can be kept together always have one potential state behind them; three relation records of which any two can be kept have none
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 HST 19:09: "Let's look to gauge to learn more about the occupant".
 RULING_occupant_forms_2026-11-14 (record form / raw form). Def_APFPaper1_RecordOccupant (this seat).
 Paper 12 v1.8 (The Gauge Sector of Admissibility Physics): lines 352-376 (an interface either admits "a
 global Boolean section" or does not; "the occupant" is the declared datum that it somewhere does not; the
 profile is read off the record and "never derived"); 564-566 (a register is "protected" when its cells
 "cannot be erased or overwritten by the substrate's free relabelings"); 2279-2334 (Step 2: a relabeling
 "that preserves every tested expectation is a free convention at zero marginal cost", the relabel-freedom
 clause, "adopted and named"; the gauge group is the group of such relabelings).
 Codebank: apf/core.py check_T_alg (the route from a joint surplus to a noncommutative record algebra is
 tagged [P+IJC]: it needs the no-section premise stated explicitly; the abstract route "does NOT logically
 go through"); apf/gauge.py check_Theorem_R, R1(e) (a zero-cost exchange makes a distinction "not robust");
 apf/gauge_quotient_ledger.py (GQL-1, a named identification, not banked: no enforceable separator pins a
 gauge-orbit position); apf/gauge_invariant_record.py (reading grade: the only sharp gauge-invariant colour
 record is the relation, not a member's side); apf/aboutness_occupancy_section.py.
standing: GENERAL LEMMAS AND ONE WORLD. Nothing here is a reading and nothing here is adopted.
what this file says:
 1. noSide_of_record_keeping_flip, no_record_keeping_flip_of_hasSide. A move of potential states that keeps
    every kept record, and flips the reading of a distinction, exists only where the occupant is in raw form
    on that distinction. In record form no such move exists. This is Paper 12's "protected" said in the
    occupant vocabulary: the free relabelings act only inside raw form.
 2. hasSection_of_one_family, hasSection_of_noSide, hasSection_of_kept_together. Raw form as typed in
    Def_APFPaper1_RecordOccupant always has a potential state behind it. More generally any record families
    that can all be kept together have one. So the definition, on one kept record set, cannot tell an
    occupant with no side from an occupant whose side is not recorded. To say "no side" in Paper 12's sense
    one needs record families that cannot all be kept together.
 3. Triangle. Three distinctions, three relation records ("these two differ"). Any two records can be kept;
    in every such pair each distinction is in raw form; the kept pair settles the third relation as "the
    same"; the three cannot be kept together; no potential state lies behind the three pairs. B02's second
    sentence (APFB02.EveryCombinationHeld) holds in this world.
what this file does NOT say:
 - That nature realizes the Triangle. It is the smallest logical world with no section. In quantum theory
   sharp tests that are pairwise compatible are jointly compatible, so this triangle does not occur there.
 - That an occupant shows both records of whichever pair is kept. That is a statement about what is
   realized in each kept set (Paper 12's "profile"), and it is what would make the Triangle an occupant
   with no side rather than three records that are never all true. It is not typed here.
 - That the eight inputs force a world with no section, or exclude one. Neither is shown.
 - Anything about a number, a carrier, a transfer or Born. No lane. No claim that the transfer is forced,
   that the carrier gap is closed or narrowed, or that Born is derived.
 - That "keeps every kept record" is the same as Paper 12's "preserves every tested expectation". Here a
   move is a map of potential states; there it is an automorphism of the record algebra.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper1_RecordOccupant
import Definitions.Def_APFB02_EachTakesBothSides
import Mathlib.Data.Finset.Insert

namespace APFPaper1.RecordOccupant

variable {X D Rec : Type*}

/-! ### Moves that no kept record sees -/

/-- A move of potential states that keeps every kept record and flips the reading of `d` puts both sides of
`d` among the allowed states: the occupant is in raw form on `d`. -/
theorem noSide_of_record_keeping_flip (reads : D → X → Bool) (allows : Rec → X → Prop) (K : Finset Rec)
    (d : D) (sigma : X → X) (hkeep : ∀ x ∈ allowed allows K, sigma x ∈ allowed allows K)
    (hflip : ∀ x, reads d (sigma x) = !reads d x) (hne : (allowed allows K).Nonempty) :
    NoSide reads allows K d := by
  obtain ⟨x, hx⟩ := hne
  cases h : reads d x with
  | true =>
      refine ⟨⟨x, hx, h⟩, ⟨sigma x, hkeep x hx, ?_⟩⟩
      simp [hflip, h]
  | false =>
      refine ⟨⟨sigma x, hkeep x hx, ?_⟩, ⟨x, hx, h⟩⟩
      simp [hflip, h]

/-- In record form on `d` there is no move that keeps every kept record and flips the reading of `d`. -/
theorem no_record_keeping_flip_of_hasSide (reads : D → X → Bool) (allows : Rec → X → Prop)
    (K : Finset Rec) (d : D) (b : Bool) (hs : HasSide reads allows K d b) (sigma : X → X)
    (hkeep : ∀ x ∈ allowed allows K, sigma x ∈ allowed allows K) :
    ¬ ∀ x, reads d (sigma x) = !reads d x := by
  intro hflip
  obtain ⟨⟨x, hx⟩, hall⟩ := hs
  have h1 := hall x hx
  have h2 := hall (sigma x) (hkeep x hx)
  rw [hflip, h1] at h2
  cases b <;> simp at h2

/-! ### One potential state behind several record sets -/



/-- A single record set that can be kept has a potential state behind it. -/
theorem hasSection_of_one_family (allows : Rec → X → Prop) (K : Finset Rec)
    (hne : (allowed allows K).Nonempty) : HasSection allows (fun _ : Unit => K) := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, fun _ => hx⟩

/-- Raw form, as typed on one kept record set, always has a potential state behind it. -/
theorem hasSection_of_noSide (reads : D → X → Bool) (allows : Rec → X → Prop) (K : Finset Rec) (d : D)
    (h : NoSide reads allows K d) : HasSection allows (fun _ : Unit => K) := by
  obtain ⟨⟨x, hx, _⟩, _⟩ := h
  exact hasSection_of_one_family allows K ⟨x, hx⟩

/-- Record families that can all be kept together have one potential state behind them. -/
theorem hasSection_of_kept_together {ι : Type*} (allows : Rec → X → Prop) (fam : ι → Finset Rec)
    (K : Finset Rec) (hsub : ∀ i, fam i ⊆ K) (hne : (allowed allows K).Nonempty) :
    HasSection allows fam := by
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, fun i => ?_⟩
  intro r hr
  exact hx r (hsub i hr)

/-- Where no potential state lies behind the families, no record set containing them all can be kept. -/
theorem not_kept_together_of_no_section {ι : Type*} (allows : Rec → X → Prop) (fam : ι → Finset Rec)
    (hno : ¬ HasSection allows fam) (K : Finset Rec) (hsub : ∀ i, fam i ⊆ K) :
    ¬ (allowed allows K).Nonempty :=
  fun hne => hno (hasSection_of_kept_together allows fam K hsub hne)

/-! ### The triangle: any two relation records can be kept, and no potential state lies behind them -/

namespace Triangle









/-- B02's second sentence holds: every combination of sides is held by some potential state. -/
theorem every_combination_held : APFB02.EveryCombinationHeld side :=
  fun _ v => ⟨v, fun _ _ => rfl⟩

/-- Turning every side over keeps every relation record. -/
theorem turnover_keeps_every_record (r : Corner) (x : Corner → Bool) (h : differ r x) :
    differ r (fun d => !x d) := by
  cases r <;> simp only [differ] at h ⊢ <;> intro hc <;> apply h <;>
    first
      | (cases h1 : x .a <;> cases h2 : x .b <;> cases h3 : x .c <;> simp_all)

/-- Any two of the three relation records can be kept. -/
theorem each_pair_can_be_kept (k : Corner) : (allowed differ (pair k)).Nonempty := by
  cases k
  · refine ⟨fun d => decide (d = Corner.a), ?_⟩
    intro r hr
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> simp [differ]
  · refine ⟨fun d => decide (d = Corner.b), ?_⟩
    intro r hr
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> simp [differ]
  · refine ⟨fun d => decide (d = Corner.c), ?_⟩
    intro r hr
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> simp [differ]

/-- In every kept pair, each of the three distinctions is in raw form. -/
theorem members_raw_in_each_pair (k d : Corner) : NoSide side differ (pair k) d :=
  noSide_of_record_keeping_flip side differ (pair k) d (fun x e => !x e)
    (fun x hx r hr => turnover_keeps_every_record r x (hx r hr)) (fun _ => rfl)
    (each_pair_can_be_kept k)

/-- A kept pair settles the third relation the other way: the two distinctions record `k` speaks of are on
the same side in every state the pair allows. -/
theorem kept_pair_settles_third_as_same (k : Corner) (x : Corner → Bool)
    (hx : x ∈ allowed differ (pair k)) : ¬ differ k x := by
  cases k
  · have hb : differ .b x := hx .b (by simp [pair])
    have hc : differ .c x := hx .c (by simp [pair])
    simp only [differ] at hb hc ⊢
    cases h1 : x .a <;> cases h2 : x .b <;> cases h3 : x .c <;> simp_all
  · have hc : differ .c x := hx .c (by simp [pair])
    have ha : differ .a x := hx .a (by simp [pair])
    simp only [differ] at hc ha ⊢
    cases h1 : x .a <;> cases h2 : x .b <;> cases h3 : x .c <;> simp_all
  · have ha : differ .a x := hx .a (by simp [pair])
    have hb : differ .b x := hx .b (by simp [pair])
    simp only [differ] at ha hb ⊢
    cases h1 : x .a <;> cases h2 : x .b <;> cases h3 : x .c <;> simp_all

/-- No potential state lies behind the three pairs. -/
theorem no_section : ¬ HasSection differ pair := by
  rintro ⟨x, hx⟩
  have ha : differ .a x := hx .b .a (by simp [pair])
  exact kept_pair_settles_third_as_same .a x (hx .a) ha

/-- The three relation records cannot be kept together. -/
theorem three_cannot_be_kept : ¬ (allowed differ ({.a, .b, .c} : Finset Corner)).Nonempty := by
  refine not_kept_together_of_no_section differ pair no_section _ ?_
  intro i
  cases i <;> intro r hr <;> simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hr ⊢ <;>
    rcases hr with rfl | rfl <;> simp

end Triangle

end APFPaper1.RecordOccupant


theorem solution :
Not
  (@Set.Nonempty.{0} (APFPaper1.RecordOccupant.Triangle.Corner → Bool)
    (@APFPaper1.RecordOccupant.allowed.{0, 0} (APFPaper1.RecordOccupant.Triangle.Corner → Bool)
      APFPaper1.RecordOccupant.Triangle.Corner APFPaper1.RecordOccupant.Triangle.differ
      (@Insert.insert.{0, 0} APFPaper1.RecordOccupant.Triangle.Corner
        (Finset.{0} APFPaper1.RecordOccupant.Triangle.Corner)
        (@Finset.instInsert.{0} APFPaper1.RecordOccupant.Triangle.Corner
          APFPaper1.RecordOccupant.Triangle.instDecidableEqCorner)
        APFPaper1.RecordOccupant.Triangle.Corner.a
        (@Insert.insert.{0, 0} APFPaper1.RecordOccupant.Triangle.Corner
          (Finset.{0} APFPaper1.RecordOccupant.Triangle.Corner)
          (@Finset.instInsert.{0} APFPaper1.RecordOccupant.Triangle.Corner
            APFPaper1.RecordOccupant.Triangle.instDecidableEqCorner)
          APFPaper1.RecordOccupant.Triangle.Corner.b
          (@Singleton.singleton.{0, 0} APFPaper1.RecordOccupant.Triangle.Corner
            (Finset.{0} APFPaper1.RecordOccupant.Triangle.Corner)
            (@Finset.instSingleton.{0} APFPaper1.RecordOccupant.Triangle.Corner)
            APFPaper1.RecordOccupant.Triangle.Corner.c))))) := by
  exact @APFPaper1.RecordOccupant.Triangle.three_cannot_be_kept

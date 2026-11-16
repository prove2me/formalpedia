-- Prove2me | solution 1 for APFPaper1.RecordOccupant.not_hasSide_of_noSide
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:25:30.784977+00:00
-- url     : https://prove2.me/submissions/74ffb3c8-0cc3-43ee-b806-bb44971bb4b5

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper1_RecordOccupant_sides
title: On each distinction the occupant is in record form (a side) or in raw form (none), never both; records that speak of other distinctions leave a distinction without a side; a recorded relation leaves both its members without a side; and the distinctions with a side number at most the records kept
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFPaper1_RecordOccupant (this seat). FOUNDATION_INPUTS B02, second sentence, in the builder
 seat's finite-set form APFB02.EveryCombinationHeld (Def_APFB02_EachTakesBothSides). The author's reading of
 2026-11-13 17:23 HST and this seat's adopted sentence 5 (a held relation is free of the distinctions it
 sits over). Paper 1 Supplement v9.28:3625 (the count of resolved classes is at most capacity over floor).
 The author, 2026-11-14 18:55 and 18:57 HST (RULING_occupant_forms_2026-11-14): on a distinction with no
 record the occupant itself has no side. The bundle v18 header of this file said these were statements
 about the records and not the occupant; that was this seat's misreading and is withdrawn. Codebank apf/plec.py, check_Regime_exit_Type_III (record locking as a change of
 admissible class), found after this file was first written.
consumes_inputs: B02's second sentence, as the hypothesis hB02 in the form EveryCombinationHeld, in the
 theorems that say so. That form is the builder seat's proposed encoding; its fidelity is not certified.
named_hypotheses: allows (what each record allows) and SpeaksOnlyOf are supplied data and a supplied
 property of it. In settled_card_le_records, about and hatom (each record speaks of one distinction). In
 settled_card_mul_floor_le_cost, heps (each kept record costs at least eps).
statement: (hasSide_or_noSide) if some state is allowed, d has side true, side false, or no side.
 (not_hasSide_of_noSide) never a side and none. (hasSide_mono) keeping more records keeps every side already
 had, while some state is still allowed. (noSide_of_no_records) keeping nothing, there is no side on any
 distinction that takes both values. (noSide_of_not_spoken_of) under B02's second sentence, if the records
 speak only of the family S and d is not in S, there is no side on d. (spoken_of_of_hasSide) so a side on d
 puts d among the distinctions spoken of. (relation_recorded_members_free) under B02's second sentence, records
 consisting only of a record that two distinctions read alike have that relation fixed and no side on
 either. (relation_and_one_side_fix_the_other) with a record of one member's side kept as well, the records
 have the same side on the other. (settled_card_le_records) if each record speaks of one distinction, the distinctions
 with a side number at most the records kept. (settled_card_mul_floor_le_cost) so that number times the
 floor is at most the cost of the records kept.
not_claimed: that "no side" is more than "not fixed by the records": on this file alone the allowed states
 are a set of two-valued states, which is the shape of ignorance. What makes it absence is B07b, in
 Thm_APFB07b_no_side_without_a_record, under hypotheses that are not inputs. Nothing here is non-classical:
 every family of distinctions has a joint side for every combination, by B02. No lane. No claim that the
 transfer is forced, that the carrier gap is closed or narrowed, or that Born is derived.
-/
import Definitions.Def_APFPaper1_RecordOccupant
import Definitions.Def_APFB02_EachTakesBothSides
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper1.RecordOccupant

variable {X D Rec : Type*}

/-- If some state is allowed, `d` has side true, side false, or no side. -/
theorem hasSide_or_noSide (reads : D → X → Bool) (allows : Rec → X → Prop) (K : Finset Rec)
    (hne : (allowed allows K).Nonempty) (d : D) :
    HasSide reads allows K d true ∨ HasSide reads allows K d false ∨ NoSide reads allows K d := by
  by_cases h1 : ∃ x ∈ allowed allows K, reads d x = true
  · by_cases h2 : ∃ y ∈ allowed allows K, reads d y = false
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · refine Or.inl ⟨hne, fun x hx => ?_⟩
      cases hd : reads d x
      · exact absurd ⟨x, hx, hd⟩ h2
      · rfl
  · refine Or.inr (Or.inl ⟨hne, fun x hx => ?_⟩)
    cases hd : reads d x
    · rfl
    · exact absurd ⟨x, hx, hd⟩ h1

/-- Never a side and none. -/
theorem not_hasSide_of_noSide (reads : D → X → Bool) (allows : Rec → X → Prop) (K : Finset Rec)
    (d : D) (h : NoSide reads allows K d) (b : Bool) : ¬ HasSide reads allows K d b := by
  rintro ⟨_, hb⟩
  obtain ⟨⟨x, hx, hxt⟩, ⟨y, hy, hyf⟩⟩ := h
  have h1 := hb x hx
  have h2 := hb y hy
  rw [hxt] at h1
  rw [hyf] at h2
  rw [← h1] at h2
  exact absurd h2 (by decide)

/-- Keeping more records keeps every side already had, while some state is still allowed. -/
theorem hasSide_mono (reads : D → X → Bool) (allows : Rec → X → Prop) (K K' : Finset Rec)
    (hsub : K ⊆ K') (hne : (allowed allows K').Nonempty) (d : D) (b : Bool)
    (h : HasSide reads allows K d b) : HasSide reads allows K' d b :=
  ⟨hne, fun x hx => h.2 x (fun r hr => hx r (hsub hr))⟩

/-- Keeping nothing, there is no side on any distinction that takes both values. -/
theorem noSide_of_no_records (reads : D → X → Bool) (allows : Rec → X → Prop) (d : D)
    (hboth : (∃ x, reads d x = true) ∧ ∃ y, reads d y = false) :
    NoSide reads allows (∅ : Finset Rec) d := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hboth
  exact ⟨⟨x, fun r hr => absurd hr (Finset.notMem_empty r), hx⟩,
    ⟨y, fun r hr => absurd hr (Finset.notMem_empty r), hy⟩⟩

/-- Under B02's second sentence: if the records speak only of the family `S` and `d` is not in
`S`, there is no side on `d`. -/
theorem noSide_of_not_spoken_of [DecidableEq D] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (hB02 : APFB02.EveryCombinationHeld reads) (K : Finset Rec)
    (S : Finset D) (hsp : SpeaksOnlyOf reads allows K S) (d : D) (hd : d ∉ S)
    (hne : (allowed allows K).Nonempty) : NoSide reads allows K d := by
  obtain ⟨x, hx⟩ := hne
  have key : ∀ b : Bool, ∃ y ∈ allowed allows K, reads d y = b := by
    intro b
    obtain ⟨y, hy⟩ := hB02 (insert d S) (fun e => if e = d then b else reads e x)
    refine ⟨y, fun r hr => hsp r hr x y (fun e he => ?_) (hx r hr), ?_⟩
    · have h := hy e (Finset.mem_insert_of_mem he)
      have hne' : e ≠ d := fun h' => hd (h' ▸ he)
      rw [if_neg hne'] at h
      exact h.symm
    · have h := hy d (Finset.mem_insert_self d S)
      rw [if_pos rfl] at h
      exact h
  exact ⟨key true, key false⟩

/-- So a side on `d` puts `d` among the distinctions the records speak of. -/
theorem spoken_of_of_hasSide [DecidableEq D] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (hB02 : APFB02.EveryCombinationHeld reads) (K : Finset Rec)
    (S : Finset D) (hsp : SpeaksOnlyOf reads allows K S) (d : D) (b : Bool)
    (h : HasSide reads allows K d b) : d ∈ S := by
  by_contra hd
  exact not_hasSide_of_noSide reads allows K d
    (noSide_of_not_spoken_of reads allows hB02 K S hsp d hd h.1) b h

/-- Under B02's second sentence: records consisting only of a record that two distinctions read
alike have that relation fixed and no side on either. -/
theorem relation_recorded_members_free [DecidableEq D] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (hB02 : APFB02.EveryCombinationHeld reads) (d1 d2 : D) (r : Rec)
    (hr : ∀ x, allows r x ↔ reads d1 x = reads d2 x) :
    (allowed allows {r}).Nonempty ∧ (∀ x ∈ allowed allows {r}, reads d1 x = reads d2 x) ∧
      NoSide reads allows {r} d1 ∧ NoSide reads allows {r} d2 := by
  have hmem : ∀ x, x ∈ allowed allows ({r} : Finset Rec) ↔ reads d1 x = reads d2 x := by
    intro x
    constructor
    · intro hx
      exact (hr x).mp (hx r (Finset.mem_singleton_self r))
    · intro h s hs
      rw [Finset.mem_singleton.mp hs]
      exact (hr x).mpr h
  have key : ∀ b : Bool, ∃ x ∈ allowed allows ({r} : Finset Rec),
      reads d1 x = b ∧ reads d2 x = b := by
    intro b
    obtain ⟨x, hx⟩ := hB02 {d1, d2} (fun _ => b)
    have h1 : reads d1 x = b := hx d1 (Finset.mem_insert_self _ _)
    have h2 : reads d2 x = b :=
      hx d2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    exact ⟨x, (hmem x).mpr (h1.trans h2.symm), h1, h2⟩
  obtain ⟨xt, hxt, h1t, h2t⟩ := key true
  obtain ⟨xf, hxf, h1f, h2f⟩ := key false
  exact ⟨⟨xt, hxt⟩, fun x hx => (hmem x).mp hx, ⟨⟨xt, hxt, h1t⟩, ⟨xf, hxf, h1f⟩⟩,
    ⟨⟨xt, hxt, h2t⟩, ⟨xf, hxf, h2f⟩⟩⟩

/-- With a record of one member's side kept as well, the records have the same side on the other. -/
theorem relation_and_one_side_fix_the_other [DecidableEq D] [DecidableEq Rec]
    (reads : D → X → Bool) (allows : Rec → X → Prop) (hB02 : APFB02.EveryCombinationHeld reads)
    (d1 d2 : D) (r r1 : Rec) (b : Bool)
    (hr : ∀ x, allows r x ↔ reads d1 x = reads d2 x)
    (hr1 : ∀ x, allows r1 x ↔ reads d1 x = b) :
    HasSide reads allows {r, r1} d2 b := by
  constructor
  · obtain ⟨x, hx⟩ := hB02 {d1, d2} (fun _ => b)
    have h1 : reads d1 x = b := hx d1 (Finset.mem_insert_self _ _)
    have h2 : reads d2 x = b :=
      hx d2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    refine ⟨x, fun s hs => ?_⟩
    rcases Finset.mem_insert.mp hs with rfl | hs'
    · exact (hr x).mpr (h1.trans h2.symm)
    · rw [Finset.mem_singleton.mp hs']
      exact (hr1 x).mpr h1
  · intro x hx
    have ha := (hr x).mp (hx r (Finset.mem_insert_self _ _))
    have hb := (hr1 x).mp (hx r1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    rw [← ha]
    exact hb

/-- If each record speaks of one distinction, the distinctions with a side number at most the
records kept. -/
theorem settled_card_le_records [DecidableEq D] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (hB02 : APFB02.EveryCombinationHeld reads) (K : Finset Rec)
    (about : Rec → D)
    (hatom : ∀ r ∈ K, ∀ x y : X, reads (about r) x = reads (about r) y → allows r x → allows r y)
    (T : Finset D) (hT : ∀ d ∈ T, ∃ b, HasSide reads allows K d b) : T.card ≤ K.card := by
  have hsp : SpeaksOnlyOf reads allows K (K.image about) := by
    intro r hr x y hxy
    exact hatom r hr x y (hxy (about r) (Finset.mem_image_of_mem about hr))
  have hsub : T ⊆ K.image about := by
    intro d hd
    obtain ⟨b, hb⟩ := hT d hd
    exact spoken_of_of_hasSide reads allows hB02 K (K.image about) hsp d b hb
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- So the number of distinctions with a side, times the floor, is at most the cost of the records
kept. -/
theorem settled_card_mul_floor_le_cost [DecidableEq D] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (hB02 : APFB02.EveryCombinationHeld reads) (K : Finset Rec)
    (about : Rec → D)
    (hatom : ∀ r ∈ K, ∀ x y : X, reads (about r) x = reads (about r) y → allows r x → allows r y)
    (T : Finset D) (hT : ∀ d ∈ T, ∃ b, HasSide reads allows K d b)
    (cost : Rec → ℝ) (eps : ℝ) (heps0 : 0 ≤ eps) (heps : ∀ r ∈ K, eps ≤ cost r) :
    (T.card : ℝ) * eps ≤ ∑ r ∈ K, cost r := by
  have hcard : (T.card : ℝ) ≤ (K.card : ℝ) := by
    exact_mod_cast settled_card_le_records reads allows hB02 K about hatom T hT
  have h1 : (T.card : ℝ) * eps ≤ (K.card : ℝ) * eps := mul_le_mul_of_nonneg_right hcard heps0
  have h2 : (K.card : ℝ) * eps ≤ ∑ r ∈ K, cost r := by
    have h := Finset.card_nsmul_le_sum K cost eps heps
    rw [nsmul_eq_mul] at h
    exact h
  linarith

end APFPaper1.RecordOccupant

#print axioms APFPaper1.RecordOccupant.hasSide_or_noSide
#print axioms APFPaper1.RecordOccupant.not_hasSide_of_noSide
#print axioms APFPaper1.RecordOccupant.hasSide_mono
#print axioms APFPaper1.RecordOccupant.noSide_of_no_records
#print axioms APFPaper1.RecordOccupant.noSide_of_not_spoken_of
#print axioms APFPaper1.RecordOccupant.spoken_of_of_hasSide
#print axioms APFPaper1.RecordOccupant.relation_recorded_members_free
#print axioms APFPaper1.RecordOccupant.relation_and_one_side_fix_the_other
#print axioms APFPaper1.RecordOccupant.settled_card_le_records
#print axioms APFPaper1.RecordOccupant.settled_card_mul_floor_le_cost


universe apfNative_u_1 apfNative_u_2 apfNative_u_3
theorem solution :
∀ {X : Type apfNative_u_1} {D : Type apfNative_u_2} {Rec : Type apfNative_u_3} (reads : D → X → Bool)
  (allows : Rec → X → Prop) (K : Finset.{apfNative_u_3} Rec) (d : D)
  (h : @APFPaper1.RecordOccupant.NoSide.{apfNative_u_1, apfNative_u_2, apfNative_u_3} X D Rec reads allows K d)
  (b : Bool),
  Not (@APFPaper1.RecordOccupant.HasSide.{apfNative_u_1, apfNative_u_2, apfNative_u_3} X D Rec reads allows K d b) := by
  exact @APFPaper1.RecordOccupant.not_hasSide_of_noSide

-- Prove2me | solution 1 for APFPaper1.Source.exists_subfamily_of_subset_map
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:48:38.78295+00:00
-- url     : https://prove2.me/submissions/779b1e32-c623-416b-9300-d072793916d2

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-13; not
 gated, not reviewed, not released, not built on the build box)
name: APFPaper1_familyCost_relabel
title: Feasibility, family cost and ledger admissibility do not change when distinctions are relabelled
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFPaper1_FamilyCost. Ordinary mathematics on the definitions; consumes no input.
statement: let f carry labels t to distinctions f t, one to one. Record data given on distinctions can be
 read on labels through f. A finite family of labels then has, under the read-back data, the same serving
 protocols, the same feasibility, the same family cost and the same admissibility as its image family of
 distinctions. And for a one-to-one correspondence, every subfamily of an image family is the image of a
 subfamily.
not_claimed: anything about support novelty (not needed here); any law on the record data.
-/
import Definitions.Def_APFPaper1_FamilyCost
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Equiv.Defs

set_option autoImplicit false
namespace APFPaper1.Source

theorem serves_map_iff {D D' P Record : Type*} (f : D' ↪ D) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (p : P) (T : Finset D') :
    (∀ d ∈ T.map f, ∃ sigma : Set Record,
        sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) ↔
      (∀ t ∈ T, ∃ sigma : Set Record,
        sigma ⊆ maintained p ∧ sufficient p sigma (f t) ∧ usesToRealize p (f t) sigma) := by
  constructor
  · intro h t ht
    exact h (f t) (Finset.mem_map.mpr ⟨t, ht, rfl⟩)
  · intro h d hd
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hd
    exact h t ht

theorem familyFeasible_map_iff {D D' P Record : Type*} (f : D' ↪ D) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (T : Finset D') :
    familyFeasible maintained sufficient usesToRealize (T.map f) ↔
      familyFeasible maintained (fun p s t => sufficient p s (f t))
        (fun p t s => usesToRealize p (f t) s) T :=
  exists_congr (fun p => serves_map_iff f maintained sufficient usesToRealize p T)

theorem familyCost_map {D D' P R Record : Type*} (f : D' ↪ D)
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (T : Finset D') :
    familyCost wholeResource calibration maintained sufficient usesToRealize (T.map f) =
      familyCost wholeResource calibration maintained (fun p s t => sufficient p s (f t))
        (fun p t s => usesToRealize p (f t) s) T := by
  unfold familyCost
  congr 1
  ext c
  constructor
  · rintro ⟨p, hp, hc⟩
    exact ⟨p, (serves_map_iff f maintained sufficient usesToRealize p T).mp hp, hc⟩
  · rintro ⟨p, hp, hc⟩
    exact ⟨p, (serves_map_iff f maintained sufficient usesToRealize p T).mpr hp, hc⟩

theorem familyAdmissible_map_iff {D D' P R Record : Type*} (f : D' ↪ D)
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (C : ℝ) (T : Finset D') :
    familyAdmissible wholeResource calibration maintained sufficient usesToRealize C (T.map f) ↔
      familyAdmissible wholeResource calibration maintained (fun p s t => sufficient p s (f t))
        (fun p t s => usesToRealize p (f t) s) C T := by
  unfold familyAdmissible
  rw [familyFeasible_map_iff, familyCost_map]

/-- Under a one-to-one correspondence, every subfamily of an image family is the image of a subfamily. -/
theorem exists_subfamily_of_subset_map {D D' : Type*} (e : D' ≃ D) (T : Finset D') (S : Finset D)
    (h : S ⊆ T.map e.toEmbedding) : ∃ T' : Finset D', T' ⊆ T ∧ T'.map e.toEmbedding = S := by
  refine ⟨S.map e.symm.toEmbedding, ?_, ?_⟩
  · intro t ht
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨t', ht', hdt⟩ := Finset.mem_map.mp (h hd)
    have h1 : e.symm d = t' := by
      rw [← hdt]
      exact e.symm_apply_apply t'
    show e.symm d ∈ T
    rw [h1]
    exact ht'
  · ext d
    constructor
    · intro hd
      obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hd
      obtain ⟨d', hd', rfl⟩ := Finset.mem_map.mp ht
      show e (e.symm d') ∈ S
      rw [e.apply_symm_apply]
      exact hd'
    · intro hd
      exact Finset.mem_map.mpr ⟨e.symm d, Finset.mem_map.mpr ⟨d, hd, rfl⟩, e.apply_symm_apply d⟩

end APFPaper1.Source

#print axioms APFPaper1.Source.familyAdmissible_map_iff
#print axioms APFPaper1.Source.exists_subfamily_of_subset_map


universe apfNative_u_1 apfNative_u_2
theorem solution :
∀ {D : Type apfNative_u_1} {D' : Type apfNative_u_2} (e : Equiv.{apfNative_u_2 + 1, apfNative_u_1 + 1} D' D)
  (T : Finset.{apfNative_u_2} D') (S : Finset.{apfNative_u_1} D)
  (h :
    @LE.le.{apfNative_u_1} (Finset.{apfNative_u_1} D)
      (@Preorder.toLE.{apfNative_u_1} (Finset.{apfNative_u_1} D)
        (@PartialOrder.toPreorder.{apfNative_u_1} (Finset.{apfNative_u_1} D)
          (@Finset.instPartialOrder.{apfNative_u_1} D)))
      S
      (@Finset.map.{apfNative_u_2, apfNative_u_1} D' D
        (@Equiv.toEmbedding.{apfNative_u_2 + 1, apfNative_u_1 + 1} D' D e) T)),
  @Exists.{apfNative_u_2 + 1} (Finset.{apfNative_u_2} D') fun (T' : Finset.{apfNative_u_2} D') =>
    And
      (@LE.le.{apfNative_u_2} (Finset.{apfNative_u_2} D')
        (@Preorder.toLE.{apfNative_u_2} (Finset.{apfNative_u_2} D')
          (@PartialOrder.toPreorder.{apfNative_u_2} (Finset.{apfNative_u_2} D')
            (@Finset.instPartialOrder.{apfNative_u_2} D')))
        T' T)
      (@Eq.{apfNative_u_1 + 1} (Finset.{apfNative_u_1} D)
        (@Finset.map.{apfNative_u_2, apfNative_u_1} D' D
          (@Equiv.toEmbedding.{apfNative_u_2 + 1, apfNative_u_1 + 1} D' D e) T')
        S) := by
  exact @APFPaper1.Source.exists_subfamily_of_subset_map

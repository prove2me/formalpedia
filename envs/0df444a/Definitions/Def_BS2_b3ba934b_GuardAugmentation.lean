-- Prove2me | Definitions.Def_BS2_b3ba934b_GuardAugmentation
-- name    : BS2_b3ba934b_GuardAugmentation
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:01:14.121104+00:00
-- url     : https://prove2.me/theorems/ca848c66-30bf-4d68-a783-9fab3a367e3d
-- title:
--   Sensitivity separation: GuardAugmentation (complete source module)
-- statement:
--   Complete Lean source module `GuardAugmentation` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/GuardAugmentation.lean; original SHA-256 9f7c8a76b829f98117ee0347abbe7f6abea6b1067f3dac3c6ba994ff5ed748fe; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/-
Actual guard augmentation for graded-target candidates.

The optional matching and near-coloring argument is adapted from the accepted
CompactTournament.augment_by_guards proof in the attached Paley11987 source
(prove2.me submission 7f5aa99d-5bc6-4815-915f-ef258368885d). This module specializes
its abstract combinatorics to the actual Boolean selected-child guard sets in
TournamentHighRows and the graded target colors in CandidateCoherence.
-/
import Definitions.Def_BS2_b3ba934b_CandidateCoherence
import Mathlib.Combinatorics.Hall.Finite

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace GuardAugmentation
open scoped Classical
open Finset MinmaxLocal TournamentHighRows CandidateCoherence
noncomputable section

variable {V X : Type} [Fintype V] [DecidableEq V]

def neighbors (R : V → V → Prop) (v : V) : Finset V :=
  outNeighbors R Finset.univ v

theorem neighborhood_deficiency (R : V → V → Prop)
    (ht : ∀ x y, x ≠ y → R x y ∨ R y x) (S : Finset V) :
    S.card ≤ (S.biUnion (neighbors R)).card + 1 := by
  let U := S.biUnion (neighbors R)
  have hsmall : (S \ U).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxS,hxU⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hyS,hyU⟩ := Finset.mem_sdiff.mp hy
    by_contra hxy
    rcases ht x y hxy with he | he
    · exact hyU (Finset.mem_biUnion.mpr
        ⟨x,hxS,by simp [neighbors, outNeighbors, he]⟩)
    · exact hxU (Finset.mem_biUnion.mpr
        ⟨y,hyS,by simp [neighbors, outNeighbors, he]⟩)
  have hc := Finset.card_sdiff_add_card_inter S U
  have hi := Finset.card_le_card (Finset.inter_subset_right : S ∩ U ⊆ U)
  change S.card ≤ U.card + 1
  omega

theorem exists_optional_matching (R : V → V → Prop)
    (ht : ∀ x y, x ≠ y → R x y ∨ R y x) :
    ∃ f : V → Option V, Function.Injective f ∧
      ∀ x y, f x = some y → R x y := by
  let t : V → Finset (Option V) := fun x => insert none ((neighbors R x).image some)
  have hhall : ∀ S : Finset V, S.card ≤ (S.biUnion t).card := by
    intro S
    by_cases hS : S.Nonempty
    · have hu : S.biUnion t = insert none ((S.biUnion (neighbors R)).image some) := by
        ext z
        cases z with
        | none =>
          simp only [Finset.mem_biUnion, t, Finset.mem_insert, true_or,
            and_true, exists_prop, Finset.mem_image, reduceCtorEq, and_false,
            exists_false, or_false]
          exact iff_true_intro hS
        | some y => simp [t, Finset.mem_biUnion]
      rw [hu, Finset.card_insert_of_notMem (by simp),
        Finset.card_image_of_injective _ (Option.some_injective V)]
      exact neighborhood_deficiency R ht S
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [he]
  obtain ⟨f,hfi,hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  refine ⟨f,hfi,?_⟩
  intro x y hxy
  have hmem := hf x
  rw [hxy] at hmem
  simpa [t, neighbors, outNeighbors] using hmem

/-- A single coloring matches an outgoing arc from every vertex except
    possibly one. The matching argument also covers an empty tournament. -/
theorem exists_near_coloring (R : V → V → Prop)
    (ht : ∀ x y, x ≠ y → R x y ∨ R y x) (label : V → V → Bool) :
    ∃ (color : V → Bool) (bad : Finset V), bad.card ≤ 1 ∧
      ∀ x, x ∉ bad → ∃ y, R x y ∧ label x y = color y := by
  obtain ⟨f,hfi,hf⟩ := exists_optional_matching R ht
  let color : V → Bool := fun y =>
    if h : ∃ x, f x = some y then label (Classical.choose h) y else false
  let bad : Finset V := univ.filter fun x => f x = none
  refine ⟨color,bad,?_,?_⟩
  · apply Finset.card_le_one.mpr
    intro x hx y hy
    exact hfi ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  · intro x hx
    cases hfx : f x with
    | none => exact False.elim (hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfx⟩))
    | some y =>
      refine ⟨y,hf x y hfx,?_⟩
      have hex : ∃ z, f z = some y := ⟨x,hfx⟩
      have he : Classical.choose hex = x := hfi ((Classical.choose_spec hex).trans hfx.symm)
      simp only [color, dif_pos hex, he]

/-- Rows with one extra guard failure can be adjoined while losing at most
    one row; no target-threshold equality is used. -/
theorem augment_by_guards (R : V → V → Prop)
    (ht : ∀ x y, x ≠ y → R x y ∨ R y x)
    (ell : V → V → Bool) (C G : Finset V) (hdis : Disjoint C G)
    (q : ℕ) (base : V → Bool)
    (hC : ∀ i ∈ C, (mismatch R ell C base i).card + (outNeighbors R G i).card ≤ q)
    (hG : ∀ i ∈ G, (mismatch R ell C base i).card + (outNeighbors R G i).card ≤ q+1) :
    ∃ (S : Finset V) (color : V → Bool),
      C.card + G.card ≤ S.card + 1 ∧ OrdinaryGood R ell S q color := by
  let RG : G → G → Prop := fun i j => R i.1 j.1
  have hTG : ∀ i j : G, i ≠ j → RG i j ∨ RG j i := by
    intro i j hij
    exact ht i.1 j.1 (fun he => hij (Subtype.ext he))
  obtain ⟨colG,bad,hbad,hcover⟩ :=
    exists_near_coloring RG hTG (fun i j => ell i.1 j.1)
  let B : Finset V := bad.image Subtype.val
  have hBG : B ⊆ G := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  have hBcard : B.card ≤ 1 := (Finset.card_image_le).trans hbad
  let K := G \ B
  let S := C ∪ K
  let color : V → Bool := fun x => if hx : x ∈ G then colG ⟨x,hx⟩ else base x
  have hcolorC (x : V) (hx : x ∈ C) : color x = base x := by
    have hnot : x ∉ G := fun hg => Finset.disjoint_left.mp hdis hx hg
    simp only [color,dif_neg hnot]
  have hmatch (i : V) (hi : i ∈ K) :
      ∃ j ∈ G, R i j ∧ ell i j = color j := by
    obtain ⟨hiG,hiB⟩ := Finset.mem_sdiff.mp hi
    have hin : (⟨i,hiG⟩ : G) ∉ bad := by
      intro hb
      exact hiB (Finset.mem_image.mpr ⟨⟨i,hiG⟩,hb,rfl⟩)
    obtain ⟨j,hij,hcol⟩ := hcover ⟨i,hiG⟩ hin
    refine ⟨j.1,j.2,hij,?_⟩
    simpa only [color,dif_pos j.2] using hcol
  let charges (i : V) := mismatch R ell C base i ∪ outNeighbors R G i
  have hchargecard (i : V) : (charges i).card =
      (mismatch R ell C base i).card + (outNeighbors R G i).card := by
    apply Finset.card_union_of_disjoint
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hk).1
  have hsub (i : V) : mismatch R ell S color i ⊆ charges i := by
    intro j hj
    obtain ⟨hjS,hij,hne⟩ := Finset.mem_filter.mp hj
    rcases Finset.mem_union.mp hjS with hjC | hjK
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨hjC,hij,by simpa only [hcolorC j hjC] using hne⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨(Finset.mem_sdiff.mp hjK).1,hij⟩)
  refine ⟨S,color,?_,?_⟩
  · have hdCK : Disjoint C K := by
      apply Finset.disjoint_left.mpr
      intro i hi hk
      exact Finset.disjoint_left.mp hdis hi (Finset.mem_sdiff.mp hk).1
    have hs : S.card = C.card + K.card := Finset.card_union_of_disjoint hdCK
    have hg : K.card + B.card = G.card := Finset.card_sdiff_add_card_eq_card hBG
    omega
  · intro i hi
    rcases Finset.mem_union.mp hi with hiC | hiK
    · have hh := hC i hiC
      rw [← hchargecard i] at hh
      exact (Finset.card_le_card (hsub i)).trans hh
    · obtain ⟨j,hjG,hij,hcol⟩ := hmatch i hiK
      have hjcharges : j ∈ charges i := Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hjG,hij⟩)
      have hjnot : j ∉ mismatch R ell S color i := by
        intro hj
        exact (Finset.mem_filter.mp hj).2.2 hcol
      have herase : mismatch R ell S color i ⊆ (charges i).erase j := by
        intro y hy
        exact Finset.mem_erase.mpr ⟨fun he => hjnot (he ▸ hy),hsub i hy⟩
      have hh := hG i (Finset.mem_sdiff.mp hiK).1
      have hc := Finset.card_le_card herase
      rw [Finset.card_erase_of_mem hjcharges,hchargecard i] at hc
      omega

/-- Every abstract augmentation charge is an actual guard failure. The
    disjointness of candidates and high rows prevents double-counting. -/
theorem charges_card_le_actual_failures (R : V → V → Prop)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (C G : Finset V) (hdis : Disjoint C G) (base : V → Bool)
    (hpartner : ∀ w ∈ C, ∀ b : Bool, b ≠ base w → P (children w b))
    (hhigh : ∀ w ∈ G, ∀ b : Bool, P (children w b)) (v : V) :
    (mismatch R ell C base v).card + (outNeighbors R G v).card ≤
      (guardFailures R ell P children v).card := by
  have hd : Disjoint (mismatch R ell C base v) (outNeighbors R G v) := by
    apply Finset.disjoint_left.mpr
    intro w hwC hwG
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_filter.mp hwC).1 (Finset.mem_filter.mp hwG).1
  rw [← Finset.card_union_of_disjoint hd]
  apply Finset.card_le_card
  apply Finset.union_subset
  · exact mismatch_subset_failures R ell P children C base hpartner v
  · exact out_high_subset_failures R ell P children G hhigh v

/-- The second strengthened prefix cap: target candidates with budget q
    and disjoint high rows with budget q+1 have total size at most the
    exact ordinary-exclusion cutoff. -/
theorem target_plus_extra_high_cap (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (C G : Finset V) (hdis : Disjoint C G) (q a : ℕ)
    (hexcl : NoOrdinary R ell q a) (base : V → Bool)
    (hpartner : ∀ w ∈ C, ∀ b : Bool, b ≠ base w → P (children w b))
    (hhigh : ∀ w ∈ G, ∀ b : Bool, P (children w b))
    (hC : ∀ v ∈ C, (guardFailures R ell P children v).card ≤ q)
    (hG : ∀ v ∈ G, (guardFailures R ell P children v).card ≤ q+1) :
    C.card + G.card ≤ a := by
  have ht : ∀ x y, x ≠ y → R x y ∨ R y x := by
    intro x y hxy
    by_cases h : R x y
    · exact Or.inl h
    · exact Or.inr (by by_contra hn; exact h ((hR.orient x y hxy).mpr hn))
  have hb (v : V) := charges_card_le_actual_failures R ell P children C G hdis base
    hpartner hhigh v
  obtain ⟨S,color,hsize,hgood⟩ := augment_by_guards R ht ell C G hdis q base
    (fun v hv => (hb v).trans (hC v hv))
    (fun v hv => (hb v).trans (hG v hv))
  have hS := ordinary_card_lt R ell q a hexcl S color hgood
  omega

end
end GuardAugmentation

#print axioms GuardAugmentation.exists_optional_matching
#print axioms GuardAugmentation.exists_near_coloring
#print axioms GuardAugmentation.augment_by_guards
#print axioms GuardAugmentation.charges_card_le_actual_failures
#print axioms GuardAugmentation.target_plus_extra_high_cap



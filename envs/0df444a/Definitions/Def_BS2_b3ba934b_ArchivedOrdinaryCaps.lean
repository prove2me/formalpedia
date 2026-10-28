-- Prove2me | Definitions.Def_BS2_b3ba934b_ArchivedOrdinaryCaps
-- name    : BS2_b3ba934b_ArchivedOrdinaryCaps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T03:58:51.354084+00:00
-- url     : https://prove2.me/theorems/c5d53636-c30a-4bf8-b36d-a5437b932d5d
-- title:
--   Sensitivity separation: ArchivedOrdinaryCaps (complete source module)
-- statement:
--   Complete Lean source module `ArchivedOrdinaryCaps` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ArchivedOrdinaryCaps.lean; original SHA-256 e5bb0155feceabeb1058dbedb95b06b12a12e94f86ba9b7d02097cc1f2cd8a09; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/
import Definitions.Def_BS2_b3ba934b_ArchivedOrdinaryRepair

open OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- Sol_Paley11987Verified_CompactBooleanTransfer_candidateTotalCap_bound.lean -/
set_option autoImplicit false
set_option Elab.async false
section z8

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]





















theorem mismatch_mono (R : V → V → Prop) (ell : V × V → Fin 2)
    (A B : Finset V) (h : A ⊆ B) (color : V → Fin 2) (x : V) :
    mismatch R ell A color x ⊆ mismatch R ell B color x := by
  intro y hy
  exact Finset.mem_filter.mpr ⟨h (Finset.mem_filter.mp hy).1,
    (Finset.mem_filter.mp hy).2⟩



theorem markedGood_mono (R : V → V → Prop) (ell : V × V → Fin 2)
    (A A' M P P' : Finset V) (hA : A' ⊆ A) (hP : P' ⊆ P)
    (q B B' : ℕ) (hB : B ≤ B') (color : V → Fin 2)
    (hg : MarkedGood R ell A M P q B color) :
    MarkedGood R ell A' M P' q B' color := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (Nat.add_le_add_right
      (Finset.card_le_card (mismatch_mono R ell A' A hA color x)) _).trans
      (hg.1 x (hA hx))
  · intro y hy
    have hm := Finset.card_le_card (mismatch_mono R ell A' A hA color y)
    have ho := hg.2.1 y hy
    by_cases hyP : y ∈ P'
    · simpa only [if_pos hyP, if_pos (hP hyP), Nat.add_zero] using
        (Nat.add_le_add_left hm (outOn R M y).card).trans ho
    · simp only [if_neg hyP]
      by_cases hyold : y ∈ P
      · simp only [if_pos hyold] at ho
        omega
      · simp only [if_neg hyold] at ho
        omega
  · calc
      ∑ y ∈ M, (mismatch R ell A' color y).card ≤
          ∑ y ∈ M, (mismatch R ell A color y).card :=
        Finset.sum_le_sum fun y _ => Finset.card_le_card
          (mismatch_mono R ell A' A hA color y)
      _ ≤ B' := hg.2.2.trans hB

























end
end ZL
end
end z8

section z29

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
noncomputable section
open scoped Classical BigOperators
namespace OAI.Paper320













namespace Tournament
variable {k : ℕ} (T : Tournament k)



theorem not_adj_reverse {i j : Fin k} (h : T.Adj i j) : ¬ T.Adj j i :=
  (T.edge_compl (T.ne_of_adj h)).mp h

theorem adj_or_reverse {i j : Fin k} (h : i ≠ j) : T.Adj i j ∨ T.Adj j i := by
  by_cases hh : T.Adj j i
  · exact Or.inr hh
  · exact Or.inl ((T.edge_compl h).mpr hh)



end Tournament



















end OAI.Paper320
namespace Sensitivity205
open OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open OAI.Paper320 Sensitivity205













section Flips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

















end Flips

section RowFlips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)





end RowFlips

section Nesting
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F)





end Nesting



theorem missing_singleton {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : (missingTargets F A x i).card = 1) :
    missingTargets F A x i = {missingWitness F A x hr i} := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hi
  have hne : (missingTargets F A x i).Nonempty := hc ▸ Finset.singleton_nonempty c
  have hm : missingWitness F A x hr i ∈ missingTargets F A x i := by
    simp only [missingWitness, dif_pos hne]
    exact hne.choose_spec
  rw [hc, Finset.mem_singleton] at hm
  simpa only [hm] using hc



theorem missingWitness_unique {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : (missingTargets F A x i).card = 1) (c : Fin r)
    (hc : F A (recursiveChild x i c) = false) : c = missingWitness F A x hr i := by
  have hm := (mem_missingTargets F A x i c).mpr hc
  rwa [missing_singleton F A x hr i hi, Finset.mem_singleton] at hm

theorem missingWitness_other_true {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : (missingTargets F A x i).card = 1) (c : Fin r)
    (hc : c ≠ missingWitness F A x hr i) : F A (recursiveChild x i c) = true := by
  cases hh : F A (recursiveChild x i c)
  · exact False.elim (hc (missingWitness_unique F A x hr i hi c hh))
  · rfl

section JointCandidates








end JointCandidates





end Sensitivity2075
end
end z29

section z32
set_option maxHeartbeats 3000000
noncomputable section
open OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators
namespace OAI.Paper320.Tournament
variable {k : ℕ} (T : Tournament k)



theorem card_internalEdges (I : Finset (Fin k)) :
    (T.internalEdges I).card = I.card.choose 2 := by
  let U := T.internalEdges I
  let V := (I ×ˢ I).filter fun p => T.Adj p.2 p.1
  have hd : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact T.not_adj_reverse (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
  have hu : U.disjUnion V hd = I.offDiag := by
    ext ⟨i,j⟩
    simp only [Finset.mem_disjUnion, U, V, internalEdges, Finset.mem_filter,
      Finset.mem_product, Finset.mem_offDiag]
    constructor
    · rintro (⟨⟨hi,hj⟩,h⟩ | ⟨⟨hi,hj⟩,h⟩)
      · exact ⟨hi,hj,T.ne_of_adj h⟩
      · exact ⟨hi,hj,(T.ne_of_adj h).symm⟩
    · rintro ⟨hi,hj,hne⟩
      exact (T.adj_or_reverse hne).imp (fun h => ⟨⟨hi,hj⟩,h⟩) (fun h => ⟨⟨hi,hj⟩,h⟩)
  have hs : U.card = V.card := Finset.card_equiv (Equiv.prodComm (Fin k) (Fin k)) (by
    intro p
    simp only [U,V,internalEdges,Finset.mem_filter,Finset.mem_product,Equiv.prodComm_apply]
    tauto)
  have hc := congrArg Finset.card hu
  rw [Finset.card_disjUnion, ← hs, Finset.offDiag_card] at hc
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  change U.card = _
  omega

theorem sum_outdegree_eq (I : Finset (Fin k)) :
    ∑ i ∈ I, (I.filter (T.Adj i)).card = (T.internalEdges I).card := by
  simp only [internalEdges, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

end OAI.Paper320.Tournament
namespace SensitivityQ



















end SensitivityQ
namespace SensitivitySourceZero






















end SensitivitySourceZero
end
end z32

section z38

set_option maxHeartbeats 3000000
open scoped Classical BigOperators
noncomputable section

namespace CompactTournament
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]



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
    · exact hyU (Finset.mem_biUnion.mpr ⟨x,hxS,by simp [neighbors,he]⟩)
    · exact hxU (Finset.mem_biUnion.mpr ⟨y,hyS,by simp [neighbors,he]⟩)
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
        | some y =>
          simp [t, Finset.mem_biUnion]
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
  simpa [t, neighbors] using hmem



theorem exists_near_coloring (R : V → V → Prop)
    (ht : ∀ x y, x ≠ y → R x y ∨ R y x) (label : V → V → Fin 2) :
    ∃ (color : V → Fin 2) (bad : Finset V), bad.card ≤ 1 ∧
      ∀ x, x ∉ bad → ∃ y, R x y ∧ label x y = color y := by
  obtain ⟨f,hfi,hf⟩ := exists_optional_matching R ht
  let color : V → Fin 2 := fun y =>
    if h : ∃ x, f x = some y then label (Classical.choose h) y else 0
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



end CompactTournament
end
end z38

section z39

set_option maxHeartbeats 3000000
open scoped Classical BigOperators
noncomputable section

namespace CompactTournament
open Finset ZL
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem augment_by_guards (R : V → V → Prop)
    (ht : ∀ x y, x ≠ y → R x y ∨ R y x)
    (ell : V × V → Fin 2) (C G : Finset V) (hdis : Disjoint C G)
    (q : ℕ) (base : V → Fin 2)
    (hC : ∀ i ∈ C, (mismatch R ell C base i).card + (outOn R G i).card ≤ q)
    (hG : ∀ i ∈ G, (mismatch R ell C base i).card + (outOn R G i).card ≤ q+1) :
    ∃ (S : Finset V) (color : V → Fin 2),
      C.card + G.card ≤ S.card + 1 ∧ OrdinaryGood R ell S q color := by
  let RG : G → G → Prop := fun i j => R i.1 j.1
  have hTG : ∀ i j : G, i ≠ j → RG i j ∨ RG j i := by
    intro i j hij
    exact ht i.1 j.1 (fun he => hij (Subtype.ext he))
  obtain ⟨colG,bad,hbad,hcover⟩ :=
    exists_near_coloring RG hTG (fun i j => ell (i.1,j.1))
  let B : Finset V := bad.image Subtype.val
  have hBG : B ⊆ G := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  have hBcard : B.card ≤ 1 := (Finset.card_image_le).trans hbad
  let K := G \ B
  let S := C ∪ K
  let color : V → Fin 2 := fun x => if hx : x ∈ G then colG ⟨x,hx⟩ else base x
  have hcolorC (x : V) (hx : x ∈ C) : color x = base x := by
    have hnot : x ∉ G := fun hg => Finset.disjoint_left.mp hdis hx hg
    simp only [color,dif_neg hnot]
  have hmatch (i : V) (hi : i ∈ K) :
      ∃ j ∈ G, R i j ∧ ell (i,j) = color j := by
    obtain ⟨hiG,hiB⟩ := Finset.mem_sdiff.mp hi
    have hin : (⟨i,hiG⟩ : G) ∉ bad := by
      intro hb
      exact hiB (Finset.mem_image.mpr ⟨⟨i,hiG⟩,hb,rfl⟩)
    obtain ⟨j,hij,hcol⟩ := hcover ⟨i,hiG⟩ hin
    refine ⟨j.1,j.2,hij,?_⟩
    simpa only [color,dif_pos j.2] using hcol
  let charges (i : V) := mismatch R ell C base i ∪ outOn R G i
  have hchargecard (i : V) : (charges i).card =
      (mismatch R ell C base i).card + (outOn R G i).card := by
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

end CompactTournament
end
end z39

section z40

set_option maxHeartbeats 3000000
noncomputable section
open OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators

namespace ZT
variable {n k : ℕ} {I : Type}

theorem target_guard_disjoint (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (t g : Fin n) (q : ℕ) (x : ((Fin k × Fin 2) × I) → Bool) :
    Disjoint (tolerantTargets T label F t g q x)
      (tolerantGuards T label F t g q x) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hone := (Finset.mem_filter.mp hi).2.1
  have hempty := (Finset.mem_filter.mp hj).2.1
  simp only [hempty, Finset.card_empty] at hone
  omega

theorem positive_or_guard_full (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q : ℕ) (x : ((Fin k × Fin 2) × I) → Bool)
    (j : Fin k)
    (hj : j ∈ SensitivityQ.positiveTargets T label F t g q x (by decide) ∪
      tolerantGuards T label F t g q x) :
    ∀ c, F g (recursiveChild x j c) = true := by
  intro c
  rcases Finset.mem_union.mp hj with hp | hg
  · obtain ⟨hjt,hgate⟩ := Finset.mem_filter.mp hp
    by_cases hc : c = missingWitness F t x (by decide) j
    · simpa only [hc] using hgate
    · exact hF.accepts_of_le hgt
        (missingWitness_other_true F t x (by decide) j
          (Finset.mem_filter.mp hjt).2.1 c hc)
  · exact hF.accepts_of_le hgt
      ((missingTargets_empty F t x j).mp (Finset.mem_filter.mp hg).2.1 c)

theorem target_mismatch_failed (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q : ℕ) (x : ((Fin k × Fin 2) × I) → Bool)
    (A : Finset (Fin k)) (hA : A ⊆ tolerantTargets T label F t g q x)
    (i : Fin k) :
    ZL.mismatch T.Adj (fun e => label e.1 e.2) A
      (missingWitness F t x (by decide)) i ⊆ failedGuards T label F g x i := by
  intro j hj
  obtain ⟨hjA,hij,hl⟩ := Finset.mem_filter.mp hj
  exact (mem_failedGuards T label F g x i j).mpr ⟨hij,
    hF.accepts_of_le hgt (missingWitness_other_true F t x (by decide) j
      (Finset.mem_filter.mp (hA hjA)).2.1 _ hl)⟩

theorem targets_ordinaryGood (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q : ℕ) (x : ((Fin k × Fin 2) × I) → Bool) :
    ZL.OrdinaryGood T.Adj (fun e => label e.1 e.2)
      (tolerantTargets T label F t g q x) q (missingWitness F t x (by decide)) := by
  intro i hi
  exact (Finset.card_le_card
    (target_mismatch_failed T label F hF t g hgt q x _ (fun _ h => h) i)).trans
    (Finset.mem_filter.mp hi).2.2

theorem candidate_local_charge (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q : ℕ) (x : ((Fin k × Fin 2) × I) → Bool)
    (A M : Finset (Fin k)) (hA : A ⊆ tolerantTargets T label F t g q x)
    (hM : M ⊆ SensitivityQ.positiveTargets T label F t g q x (by decide) ∪
      tolerantGuards T label F t g q x) (hdis : Disjoint A M) (i : Fin k) :
    (ZL.mismatch T.Adj (fun e => label e.1 e.2) A
      (missingWitness F t x (by decide)) i).card +
      (ZL.outOn T.Adj M i).card ≤ (failedGuards T label F g x i).card := by
  let D := ZL.mismatch T.Adj (fun e => label e.1 e.2) A
    (missingWitness F t x (by decide)) i
  let O := ZL.outOn T.Adj M i
  have hD : D ⊆ failedGuards T label F g x i :=
    target_mismatch_failed T label F hF t g hgt q x A hA i
  have hO : O ⊆ failedGuards T label F g x i := by
    intro j hj
    obtain ⟨hjM,hij⟩ := Finset.mem_filter.mp hj
    exact (mem_failedGuards T label F g x i j).mpr
      ⟨hij, positive_or_guard_full T label F hF t g hgt q x j (hM hjM) _⟩
  have hd : Disjoint D O := by
    apply Finset.disjoint_left.mpr
    intro j hjD hjO
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_filter.mp hjD).1 (Finset.mem_filter.mp hjO).1
  calc
    D.card + O.card = (D ∪ O).card := (Finset.card_union_of_disjoint hd).symm
    _ ≤ (failedGuards T label F g x i).card :=
      Finset.card_le_card (Finset.union_subset hD hO)

theorem candidates_markedGood (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q B : ℕ) (x : ((Fin k × Fin 2) × I) → Bool)
    (A M P : Finset (Fin k)) (hA : A ⊆ tolerantTargets T label F t g q x)
    (hM : M ⊆ SensitivityQ.positiveTargets T label F t g q x (by decide) ∪
      tolerantGuards T label F t g q x)
    (hP : P ⊆ SensitivityQ.positiveTargets T label F t g q x (by decide))
    (hdis : Disjoint A M)
    (hB : (∑ y ∈ M, (ZL.mismatch T.Adj
      (fun e => label e.1 e.2) A (missingWitness F t x (by decide)) y).card) ≤ B) :
    ZL.MarkedGood T.Adj (fun e => label e.1 e.2)
      A M P q B (missingWitness F t x (by decide)) := by
  refine ⟨?_,?_,hB⟩
  · intro i hi
    exact (candidate_local_charge T label F hF t g hgt q x A M hA hM hdis i).trans
      (Finset.mem_filter.mp (hA hi)).2.2
  · intro i hi
    have hcharge := candidate_local_charge T label F hF t g hgt q x A M hA hM hdis i
    rw [Nat.add_comm] at hcharge
    by_cases hip : i ∈ P
    · simp only [if_pos hip, Nat.add_zero]
      exact hcharge.trans (Finset.mem_filter.mp (Finset.mem_filter.mp (hP hip)).1).2.2
    · simp only [if_neg hip]
      rcases Finset.mem_union.mp (hM hi) with hiU | hiG
      · have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hiU).1).2.2
        omega
      · have hh := (Finset.mem_filter.mp hiG).2.2
        omega

theorem targets_card_of_exclusion (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q w : ℕ) (hd : SensitivityQ.DefectBound T label q w)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (tolerantTargets T label F t g q x).card < w := by
  exact hd _ _ (targets_ordinaryGood T label F hF t g hgt q x)

theorem targets_guards_card_of_exclusion (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q w : ℕ) (hd : SensitivityQ.DefectBound T label q w)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (tolerantTargets T label F t g q x).card +
      (tolerantGuards T label F t g q x).card ≤ w := by
  let C := tolerantTargets T label F t g q x
  let G := tolerantGuards T label F t g q x
  have hdis : Disjoint C G := target_guard_disjoint T label F t g q x
  have hcharge (i : Fin k) := candidate_local_charge T label F hF t g hgt q x C G
    (fun _ h => h) (fun _ h => Finset.mem_union_right _ h) hdis i
  obtain ⟨S,color,hcard,hgood⟩ := CompactTournament.augment_by_guards T.Adj
    (fun _ _ h => T.adj_or_reverse h) (fun e => label e.1 e.2) C G hdis q
    (missingWitness F t x (by decide))
    (fun i hi => (hcharge i).trans (Finset.mem_filter.mp hi).2.2)
    (fun i hi => (hcharge i).trans (Nat.le_of_eq (Finset.mem_filter.mp hi).2.2))
  have hs := hd S color hgood
  change C.card + G.card ≤ w
  omega

end ZT
end
end z40

section z43

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ ZL
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]





theorem candidate_marked_unrestricted (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (A M P : Finset (Fin k))
    (hA : A ⊆ tolerantTargets T label F t g q x)
    (hM : M ⊆ positiveTargets T label F t g q x (by decide) ∪ tolerantGuards T label F t g q x)
    (hP : P ⊆ positiveTargets T label F t g q x (by decide)) (hdis : Disjoint A M) :
    MarkedGood T.Adj (fun e => label e.1 e.2) A M P q (M.card*(q+1))
      (missingWitness F t x (by decide)) := by
  apply candidates_markedGood T label F hF t g hgt q (M.card*(q+1)) x A M P hA hM hP hdis
  calc
    _ ≤ ∑ _v ∈ M, (q+1) := by
      apply Finset.sum_le_sum
      intro v hv
      have hsub := Finset.card_le_card (target_mismatch_failed T label F hF t g hgt q x A hA v)
      rcases Finset.mem_union.mp (hM hv) with hp | hg
      · have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2
        omega
      · have hh := (Finset.mem_filter.mp hg).2.2
        omega
    _ = _ := by simp

theorem targets_card_guard_marked (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q r w : ℕ)
    (hcap : MarkedCardBound T label q r 0 (r*(q+1)) w)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hr : r ≤ (tolerantGuards T label F t g q x).card) :
    (tolerantTargets T label F t g q x).card < w := by
  obtain ⟨M,hM,hcard⟩ := Finset.exists_subset_card_eq hr
  let A := tolerantTargets T label F t g q x
  have hdis : Disjoint A M := (target_guard_disjoint T label F t g q x).mono_right hM
  have hg := candidate_marked_unrestricted T label F hF t g hgt q x A M ∅
    (Finset.Subset.refl _) (fun v hv => Finset.mem_union_right _ (hM hv)) (Finset.empty_subset _) hdis
  rw [hcard] at hg
  exact hcap A M ∅ _ hdis (Finset.empty_subset _) hcard rfl hg

theorem targets_card_positive_marked (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q r w : ℕ)
    (hcap : MarkedCardBound T label q r 0 (r*(q+1)) w)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hr : r ≤ (positiveTargets T label F t g q x (by decide)).card) :
    (tolerantTargets T label F t g q x).card < w+r := by
  obtain ⟨M,hM,hcard⟩ := Finset.exists_subset_card_eq hr
  let TC := tolerantTargets T label F t g q x
  let A := TC \ M
  have hMT : M ⊆ TC := hM.trans (Finset.filter_subset _ _)
  have hdis : Disjoint A M := Finset.sdiff_disjoint
  have hg := candidate_marked_unrestricted T label F hF t g hgt q x A M ∅
    Finset.sdiff_subset (fun v hv => Finset.mem_union_left _ (hM hv)) (Finset.empty_subset _) hdis
  rw [hcard] at hg
  have hc := hcap A M ∅ _ hdis (Finset.empty_subset _) hcard rfl hg
  have hs := Finset.card_sdiff_add_card_eq_card hMT
  change A.card+M.card=TC.card at hs
  change TC.card < _
  omega

theorem targets_card_three_positive_one (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (w : ℕ)
    (hcap : MarkedCardBound T label 1 3 0 0 w)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hr : 3 ≤ (positiveTargets T label F t g 1 x (by decide)).card) :
    (tolerantTargets T label F t g 1 x).card < w+3 := by
  obtain ⟨M,hM,hcard⟩ := Finset.exists_subset_card_eq hr
  let TC := tolerantTargets T label F t g 1 x
  let A := TC \ M
  let color := missingWitness F t x (by decide)
  have hMT : M ⊆ TC := hM.trans (Finset.filter_subset _ _)
  have hdis : Disjoint A M := Finset.sdiff_disjoint
  have hg := candidate_marked_unrestricted T label F hF t g hgt 1 x A M M
    Finset.sdiff_subset (fun v hv => Finset.mem_union_left _ (hM hv)) hM hdis
  have hsum : (∑ y ∈ M, (outOn T.Adj M y).card)+
      (∑ y ∈ M, (mismatch T.Adj (fun e => label e.1 e.2) A color y).card) ≤ M.card := by
    rw [←Finset.sum_add_distrib]
    calc
      _ ≤ ∑ _y ∈ M, 1 := by
        apply Finset.sum_le_sum
        intro y hy
        simpa only [if_pos hy,Nat.add_zero] using hg.2.1 y hy
      _ = M.card := by simp
  have hi : (∑ y ∈ M, (outOn T.Adj M y).card) = 3 := by
    change (∑ y ∈ M, (M.filter (T.Adj y)).card)=3
    rw [T.sum_outdegree_eq,T.card_internalEdges,hcard]
    decide
  have hcross : (∑ y ∈ M, (mismatch T.Adj (fun e => label e.1 e.2) A color y).card) ≤ 0 := by
    rw [hi,hcard] at hsum
    omega
  have hg0 : MarkedGood T.Adj (fun e => label e.1 e.2) A M M 1 0 color :=
    ⟨hg.1,hg.2.1,hcross⟩
  have hgloose := markedGood_mono T.Adj (fun e => label e.1 e.2)
    A A M M ∅ (Finset.Subset.refl _) (Finset.empty_subset _) 1 0 0 (le_refl 0) color hg0
  have hc := hcap A M ∅ color hdis (Finset.empty_subset _) hcard rfl hgloose
  have hs := Finset.card_sdiff_add_card_eq_card hMT
  change A.card+M.card=TC.card at hs
  change TC.card < _
  omega







end ZT
end
end z43

section z45

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]





theorem _root_.ThreeBoundOrdinaryArchive.Paley11987Verified.CompactBooleanTransfer.candidateTotalCap_bound (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (hCaps : LabelCaps T label) (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q : ℕ) (hq : 0 < q) (hq8 : q ≤ 8)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (tolerantTargets T label F t g q x).card ≤
      candidateTotalCap q (tolerantGuards T label F t g q x).card
        (positiveTargets T label F t g q x (by decide)).card := by
  let C := tolerantTargets T label F t g q x
  let G := tolerantGuards T label F t g q x
  let P := positiveTargets T label F t g q x (by decide)
  have hordinary := targets_card_of_exclusion T label F hF t g hgt q (cutoff q) (hCaps.ordinary q hq8) x
  change C.card < cutoff q at hordinary
  have hord : C.card ≤ cutoff q-1 := by omega
  have hg : C.card+G.card ≤ cutoff q := targets_guards_card_of_exclusion
    T label F hF t g hgt q (cutoff q) (hCaps.ordinary q hq8) x
  have hguard : 0 < G.card → C.card ≤ guardCap q := by
    intro hgn
    by_cases hq4 : q ≤ 4
    · have hc := targets_card_guard_marked T label F hF t g hgt q 1 (guardCap q+1)
        (by simpa using hCaps.one q hq hq4) x hgn
      change C.card < guardCap q+1 at hc
      omega
    · have hq5 : 5 ≤ q := by omega
      have he : guardCap q = cutoff q-1 := by interval_cases q <;> decide
      rw [he]
      exact hord
  have hpositive : 0 < P.card → C.card ≤ targetCap q := by
    intro hpn
    by_cases hq4 : q ≤ 4
    · have hc := targets_card_positive_marked T label F hF t g hgt q 1 (guardCap q+1)
        (by simpa using hCaps.one q hq hq4) x hpn
      change C.card < (guardCap q+1)+1 at hc
      have he : targetCap q = guardCap q+1 := by interval_cases q <;> decide
      rw [he]
      omega
    · have hq5 : 5 ≤ q := by omega
      have he : targetCap q = cutoff q-1 := by interval_cases q <;> decide
      rw [he]
      exact hord
  have hu2 : q=1 ∧ 2 ≤ P.card → C.card ≤ 28 := by
    rintro ⟨rfl,hp⟩
    have hc := targets_card_positive_marked T label F hF t g hgt 1 2 27 hCaps.two_one x hp
    change C.card < 27+2 at hc
    omega
  have hu3 : q=1 ∧ 3 ≤ P.card → C.card ≤ 26 := by
    rintro ⟨rfl,hp⟩
    have hc := targets_card_three_positive_one T label F hF t g hgt 24 hCaps.zero_one_three x hp
    change C.card < 24+3 at hc
    omega
  have hg2 : q=1 ∧ 2 ≤ G.card → C.card ≤ 26 := by
    rintro ⟨rfl,hg⟩
    have hc := targets_card_guard_marked T label F hF t g hgt 1 2 27 hCaps.two_one x hg
    change C.card < 27 at hc
    omega
  have hg22 : q=2 ∧ 2 ≤ G.card → C.card ≤ 33 := by
    rintro ⟨rfl,hg⟩
    have hc := targets_card_guard_marked T label F hF t g hgt 2 2 34 hCaps.two_two x hg
    change C.card < 34 at hc
    omega
  let base := if G.card > 0 then min (cutoff q-G.card) (guardCap q) else cutoff q-1
  have hb : C.card ≤ base := by
    dsimp [base]
    split_ifs with hgn
    · exact le_min (by omega) (hguard hgn)
    · exact hord
  let pp := if P.card > 0 then min base (targetCap q) else base
  have hp : C.card ≤ pp := by
    dsimp [pp]
    split_ifs with hpn
    · exact le_min hb (hpositive hpn)
    · exact hb
  let pp2 := if q=1 ∧ P.card≥2 then min pp 28 else pp
  have hp2 : C.card ≤ pp2 := by
    dsimp [pp2]
    split_ifs with h
    · exact le_min hp (hu2 h)
    · exact hp
  let pp3 := if q=1 ∧ P.card≥3 then min pp2 26 else pp2
  have hp3 : C.card ≤ pp3 := by
    dsimp [pp3]
    split_ifs with h
    · exact le_min hp2 (hu3 h)
    · exact hp2
  let gg2 := if q=1 ∧ G.card≥2 then min pp3 26 else pp3
  have hgg2 : C.card ≤ gg2 := by
    dsimp [gg2]
    split_ifs with h
    · exact le_min hp3 (hg2 h)
    · exact hp3
  change C.card ≤ if q=2 ∧ G.card≥2 then min gg2 33 else gg2
  split_ifs with h
  · exact le_min hgg2 (hg22 h)
  · exact hgg2



end ZT
end
end z45

end ThreeBoundOrdinaryArchive



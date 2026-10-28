-- Prove2me | Definitions.Def_BS2_b3ba934b_ArchivedExclusionBridge
-- name    : BS2_b3ba934b_ArchivedExclusionBridge
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T03:59:41.814652+00:00
-- url     : https://prove2.me/theorems/c8fb8317-e3ed-4be0-b16d-6bf59c8a9a05
-- title:
--   Sensitivity separation: ArchivedExclusionBridge (complete source module)
-- statement:
--   Complete Lean source module `ArchivedExclusionBridge` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ArchivedExclusionBridge.lean; original SHA-256 39791351f29a237eb7cc87fdc561a0b53aa8335c8d813157bbe79e726eb9c567; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/
import Definitions.Def_BS2_b3ba934b_ArchivedOrdinaryCaps

open OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- selected_exists_labelCaps sections z8,z46 -/
set_option autoImplicit false
set_option Elab.async false
section z8

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]





















theorem ordinaryGood_mono (R : V → V → Prop) (ell : V × V → Fin 2)
    (A B : Finset V) (h : A ⊆ B) (q : ℕ) (color : V → Fin 2)
    (hg : OrdinaryGood R ell B q color) : OrdinaryGood R ell A q color := by
  intro x hx
  exact (Finset.card_le_card (mismatch_mono R ell A B h color x)).trans (hg x (h hx))

end
end ZL
end
end z8

section z46

set_option maxHeartbeats 600000
open scoped Classical BigOperators
noncomputable section

namespace ZT
open OAI.Paper320 ZL SensitivityQ
variable {k : ℕ}

theorem ordinary_exclusion_defect_bound (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (q a : ℕ)
    (h : ∀ I : OrdinaryIndex (Fin k) a,
      ¬ (ordinaryFamily T.Adj q a).bad I (fun e => label e.1 e.2)) :
    DefectBound T label q a := by
  intro S color hg
  by_contra hn
  obtain ⟨A,hA,hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  let I : OrdinaryIndex (Fin k) a :=
    ⟨A,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hcard⟩⟩
  apply h I
  exact ⟨color,ordinaryGood_mono T.Adj (fun e => label e.1 e.2) A S hA q color hg⟩

theorem marked_exclusion_card_bound (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (q a m B : ℕ)
    (h : ∀ I : MarkedIndex (Fin k) a m,
      ¬ (markedFamily T.Adj q a m B).bad I (fun e => label e.1 e.2)) :
    MarkedCardBound T label q m 0 B a := by
  intro A M P color hdis hPM hM hP hg
  have hpempty : P = ∅ := Finset.card_eq_zero.mp hP
  subst P
  by_contra hn
  obtain ⟨A',hA',hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  have hcompl : A' ⊆ Mᶜ := by
    intro x hx
    exact Finset.mem_compl.mpr (fun hm => Finset.disjoint_left.mp hdis (hA' hx) hm)
  let MI : (Finset.univ : Finset (Fin k)).powersetCard m :=
    ⟨M,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hM⟩⟩
  let I : MarkedIndex (Fin k) a m :=
    ⟨MI,⟨A',Finset.mem_powersetCard.mpr ⟨hcompl,hcard⟩⟩⟩
  apply h I
  exact ⟨color,markedGood_mono T.Adj (fun e => label e.1 e.2)
    A A' M ∅ ∅ hA' (Finset.Subset.refl _) q B B le_rfl color hg⟩

theorem coherent_restrict {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) (ell : V × V → Fin 2) (A A' M : Finset V)
    (hA : A' ⊆ A) (color : V → Fin 2) (hg : Coherent R ell A M color) :
    Coherent R ell A' M color := by
  intro e he
  apply hg e
  rcases Finset.mem_union.mp he with hi | hc
  · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp hi
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hA hx,hA hy⟩,hr⟩)
  · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp hc
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hx,hA hy⟩,hr⟩)

theorem dominator_exclusion_double_bound (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (a : ℕ)
    (h : ∀ I : DominatorIndex T.Adj a,
      ¬ (dominatorFamily T.Adj a).bad I (fun e => label e.1 e.2)) :
    DoubleCardBound T label a := by
  intro A M color hg
  by_contra hn
  obtain ⟨A',hA',hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  have hdom : A' ⊆ dominatedBy T.Adj M := by
    intro y hy
    simp only [dominatedBy,Finset.mem_filter,Finset.mem_univ,true_and]
    exact fun x hx => hg.2.2.1 x hx y (hA' hy)
  let MI : (Finset.univ : Finset (Fin k)).powersetCard 2 :=
    ⟨M,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hg.2.1⟩⟩
  let I : DominatorIndex T.Adj a :=
    ⟨MI,⟨A',Finset.mem_powersetCard.mpr ⟨hdom,hcard⟩⟩⟩
  apply h I
  exact ⟨color,coherent_restrict T.Adj (fun e => label e.1 e.2) A A' M hA' color hg.2.2.2⟩

theorem source_exclusion_source_bound (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (a : ℕ)
    (h : ∀ I : SourceIndex T.Adj a,
      ¬ (sourceFamily T.Adj a).bad I (fun e => label e.1 e.2)) :
    SensitivitySourceZero.SourceBound T label (a+1) := by
  intro S color hsource hzero
  obtain ⟨s,hs,hdom⟩ := hsource
  by_contra hn
  have hsizing : a ≤ (S.erase s).card := by
    rw [Finset.card_erase_of_mem hs]
    omega
  obtain ⟨A,hA,hcard⟩ := Finset.exists_subset_card_eq hsizing
  have hAS : A ⊆ S := hA.trans (Finset.erase_subset s S)
  have hAout : A ⊆ outOn T.Adj Finset.univ s := by
    intro y hy
    have hey := Finset.mem_erase.mp (hA hy)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdom y hey.2 hey.1⟩
  have hcoh : ∀ i ∈ S, ∀ j ∈ S, T.Adj i j → label i j = color j := by
    intro i hi j hj hij
    by_contra hne
    have hm : j ∈ S.filter (fun z => T.Adj i z ∧ label i z ≠ color z) :=
      Finset.mem_filter.mpr ⟨hj,hij,hne⟩
    have hp := Finset.card_pos.mpr ⟨j,hm⟩
    have hz := hzero i hi
    omega
  let I : SourceIndex T.Adj a := ⟨s,⟨A,Finset.mem_powersetCard.mpr ⟨hAout,hcard⟩⟩⟩
  apply h I
  refine ⟨color,?_⟩
  intro e he
  rcases Finset.mem_union.mp he with hi | hc
  · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp hi
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    exact hcoh e.1 (hAS hx) e.2 (hAS hy) hr
  · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp hc
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    have heq : e.1 = s := Finset.mem_singleton.mp hx
    exact hcoh e.1 (heq.symm ▸ hs) e.2 (hAS hy) hr

end ZT
end
end z46


end ThreeBoundOrdinaryArchive



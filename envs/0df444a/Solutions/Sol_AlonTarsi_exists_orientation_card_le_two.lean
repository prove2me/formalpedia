-- Prove2me | solution 1 for AlonTarsi.exists_orientation_card_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:06.960788+00:00
-- url     : https://prove2.me/submissions/d5c2a7aa-aa16-4b3a-95fd-84570ba700e5

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Definitions.Def_AlonTarsiLib_GraphPolynomial
public import Definitions.Def_AlonTarsiLib_PlanarSparse
public import Definitions.Def_AlonTarsiLib_AlonTarsi
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_MinorModel_SameBranch_trans
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_map
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_symm
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_trans
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_dartSymm_apply
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_restrict_adj
attribute [local simp] LeanPool.K5MinorFreeChoosability.dartSymm_apply
attribute [local simp] LeanPool.K5MinorFreeChoosability.restrict_adj



set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open AlonTarsi
variable {V : Type*} [Fintype V] [DecidableEq V]
open Classical
namespace AlonTarsi
theorem _root_.solution (G : SimpleGraph V)
    (hsp : ∀ s : Finset (Sym2 V), (∀ e ∈ s, e ∈ G.edgeSet) → #s ≤ 2 * #{v | ∃ e ∈ s, v ∈ e}) :
    ∃ D : V → V → Prop, IsOrientation G D ∧ ∀ v, #{w | D v w} ≤ 2 := by
  let t : G.edgeSet → Finset (V × Bool) := fun e => univ.filter fun p => p.1 ∈ (e : Sym2 V)
  have hHall : ∀ s : Finset G.edgeSet, #s ≤ #(s.biUnion t) := by
    intro s
    have h := hsp (s.map (Function.Embedding.subtype _)) (fun e he => by
      obtain ⟨e', _, rfl⟩ := Finset.mem_map.1 he
      exact e'.2)
    have hb : s.biUnion t =
        ({v | ∃ e ∈ s.map (Function.Embedding.subtype _), v ∈ e} : Finset V) ×ˢ univ := by
      ext ⟨v, b⟩
      simp [t]
    rw [hb, Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm]
    rwa [Finset.card_map] at h
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hHall
  have hfmem : ∀ e : G.edgeSet, (f e).1 ∈ e.1 := fun e => by
    have := hft e
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  let D : V → V → Prop := fun u w => ∃ h : G.Adj u w, (f ⟨s(u, w), G.mem_edgeSet.2 h⟩).1 = u
  have hsymm : ∀ u w (h : G.Adj u w),
      (⟨s(w, u), G.mem_edgeSet.2 h.symm⟩ : G.edgeSet) = ⟨s(u, w), G.mem_edgeSet.2 h⟩ :=
    fun u w h => Subtype.ext Sym2.eq_swap
  refine ⟨D, ⟨fun u w h => h.1, fun u w h => ?_, fun u w h h' => ?_⟩, fun u => ?_⟩
  · have := hfmem ⟨s(u, w), G.mem_edgeSet.2 h⟩
    rcases Sym2.mem_iff.1 this with h1 | h1
    · exact Or.inl ⟨h, h1⟩
    · exact Or.inr ⟨h.symm, by rw [hsymm u w h]; exact h1⟩
  · obtain ⟨h1, h2⟩ := h
    obtain ⟨_, h3⟩ := h'
    rw [hsymm u w h1] at h3
    exact h1.ne (h2.symm.trans h3)
  · let g : V → Bool := fun w => if h : G.Adj u w then (f ⟨s(u, w), G.mem_edgeSet.2 h⟩).2
      else false
    refine le_trans (Finset.card_le_card_of_injOn (t := (univ : Finset Bool)) g
      (fun _ _ => Finset.mem_coe.2 (mem_univ _)) ?_) (by simp)
    intro w hw w' hw' hgw
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw hw'
    obtain ⟨hw1, hw2⟩ := hw
    obtain ⟨hw1', hw2'⟩ := hw'
    simp only [g, hw1, hw1', ↓reduceDIte] at hgw
    have := hfinj (Prod.ext (hw2.trans hw2'.symm) hgw)
    have := congrArg Subtype.val this
    exact (Sym2.congr_right.1 this)
end AlonTarsi

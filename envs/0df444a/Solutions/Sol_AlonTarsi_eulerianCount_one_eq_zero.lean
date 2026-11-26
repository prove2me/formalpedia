-- Prove2me | solution 1 for AlonTarsi.eulerianCount_one_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:14.825331+00:00
-- url     : https://prove2.me/submissions/daedd81e-4cd5-46ba-8648-87e96ea8ce09

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Definitions.Def_AlonTarsiLib_GraphPolynomial
public import Definitions.Def_AlonTarsiLib_PlanarSparse
public import Definitions.Def_AlonTarsiLib_AlonTarsi
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
theorem _root_.solution (G : SimpleGraph V) (D : V → V → Prop)
    (hD : IsOrientation G D) (side : V → Bool) (hside : ∀ u v, G.Adj u v → side u ≠ side v) :
    eulerianCount D 1 = 0 := by
  unfold eulerianCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro F hF ⟨hE, hodd⟩
  rw [Finset.mem_powerset] at hF
  have hFadj : ∀ p ∈ F, G.Adj p.1 p.2 := fun p hp => by
    have := hF hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact hD.1 _ _ this
  have hfib : ∀ (g : V × V → V) (b : Bool),
      #{p ∈ F | side (g p) = b} = ∑ v with side v = b, #{p ∈ F | g p = v} := by
    intro g b
    rw [Finset.card_eq_sum_card_fiberwise (f := g) (t := univ.filter fun v => side v = b)]
    · refine Finset.sum_congr rfl fun v hv => ?_
      rw [Finset.mem_filter] at hv
      rw [Finset.filter_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hp, -, h⟩; exact ⟨hp, h⟩
      · rintro ⟨hp, h⟩; exact ⟨hp, h ▸ hv.2, h⟩
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
      exact hp.2
  have h1 : #{p ∈ F | side p.1 = true} = #{p ∈ F | side p.2 = true} := by
    rw [hfib Prod.fst, hfib Prod.snd]
    exact Finset.sum_congr rfl fun v _ => hE v
  have h2 : #{p ∈ F | side p.2 = true} = #{p ∈ F | ¬ side p.1 = true} := by
    congr 1
    refine Finset.filter_congr fun p hp => ?_
    have := hside _ _ (hFadj p hp)
    revert this
    cases side p.1 <;> cases side p.2 <;> simp
  have h3 := Finset.card_filter_add_card_filter_not (s := F)
    (fun p : V × V => side p.1 = true)
  omega
end AlonTarsi

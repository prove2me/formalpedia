-- Prove2me | solution 1 for AlonTarsi.cycleCount_le_card_nonisolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:06.436413+00:00
-- url     : https://prove2.me/submissions/ff136309-895d-4b5c-8cd4-b80699e3ace7

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Nonplanar
public import Definitions.Def_AlonTarsiLib_PlanarSparse
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_symm
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_of_step


set_option autoImplicit true
@[expose] public section
public section
open Finset Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability
open AlonTarsi
variable {V : Type*}
variable {H : SimpleGraph V} {σ : Perm H.Dart} (hσ : IsRotationSystem H σ)
include hσ
namespace AlonTarsi
theorem _root_.solution [Fintype V] [DecidableRel H.Adj] :
    cycleCount σ ≤ #{v | ∃ u, H.Adj v u} := by
  unfold cycleCount numClasses
  calc Nat.card (Quotient (SameCycle.setoid σ)) ≤ Nat.card {v // ∃ u, H.Adj v u} := by
        refine Nat.card_le_card_of_injective (Quotient.lift
          (fun d : H.Dart => (⟨d.fst, d.snd, d.adj⟩ : {v // ∃ u, H.Adj v u})) ?_) ?_
        · intro a b hab
          have := sameCycle_of_step (Setoid.ker fun d : H.Dart => d.fst)
            (fun z => by rw [Setoid.ker_def]; exact (hσ.fst_apply z).symm) hab
          exact Subtype.ext this
        · intro p q hpq
          induction p using Quotient.inductionOn with
          | h a =>
          induction q using Quotient.inductionOn with
          | h b =>
          apply Quotient.sound
          exact hσ.sameCycle a b (congrArg Subtype.val hpq)
    _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
end AlonTarsi

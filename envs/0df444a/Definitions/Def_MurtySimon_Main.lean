-- Prove2me | Definitions.Def_MurtySimon_Main
-- name    : MurtySimon_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T23:19:27.095797+00:00
-- url     : https://prove2.me/theorems/26cdbf5a-16df-45dc-8a2d-88be36ec1004
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Juan Pablo Traverso Gianini (jtraverso/murty-simon-conjecture; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Murty-Simon conjecture on diameter-2-critical graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean

module
public import Definitions.Def_MurtySimon_Equality
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]
def turanEquiv (n : ℕ) : Fin n ≃ Fin ((n + 1) / 2) ⊕ Fin (n / 2) where
  toFun i := if h : i.val % 2 = 0 then Sum.inl ⟨i.val / 2, by have := i.isLt; omega⟩
    else Sum.inr ⟨i.val / 2, by have := i.isLt; omega⟩
  invFun
    | Sum.inl j => ⟨2 * j.val, by have := j.isLt; omega⟩
    | Sum.inr j => ⟨2 * j.val + 1, by have := j.isLt; omega⟩
  left_inv i := by
    by_cases h : i.val % 2 = 0
    · simp only [dif_pos h]; apply Fin.ext; dsimp only; omega
    · simp only [dif_neg h]; apply Fin.ext; dsimp only; omega
  right_inv s := by
    rcases s with j | j
    · dsimp only
      rw [dif_pos (by omega)]
      congr 1; apply Fin.ext; dsimp only; omega
    · dsimp only
      rw [dif_neg (by omega)]
      congr 1; apply Fin.ext; dsimp only; omega
def turanIso (n : ℕ) :
    turanGraph n 2 ≃g completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2)) where
  toEquiv := turanEquiv n
  map_rel_iff' {a b} := by
    rw [turanGraph_adj]
    simp only [turanEquiv, completeBipartiteGraph_adj]
    by_cases ha : a.val % 2 = 0 <;> by_cases hb : b.val % 2 = 0 <;> simp [ha, hb]
    all_goals omega
end MurtySimon



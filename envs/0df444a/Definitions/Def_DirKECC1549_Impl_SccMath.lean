-- Prove2me | Definitions.Def_DirKECC1549_Impl_SccMath
-- name    : DirKECC1549_Impl_SccMath
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-16T06:01:17.943321+00:00
-- url     : https://prove2.me/theorems/aa813262-10e3-40ad-975d-b7cb046b7d66
-- title:
--   Kosaraju's algorithm: reachability and the post-order property
-- statement:
--   Reachability `Reach`, the post-order property `KP` of vertex positions (every out-edge goes to a later-finished vertex or one reaching back), the depth-first search invariant `DfsH`, and sortedness lemmas for blocks of positions.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model (p.25). Definitions of the verified word-RAM implementation of Algorithm 3.

import Definitions.Def_DirKECC1549_Impl_GraphAux

set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main DirKECC1549.Main.CostAux

variable {n m : ℕ}

/-- The post-order property of a depth-first search (`pos` = finishing position). -/
def KP (D : Fin m → Fin n × Fin n) (pos : Fin n → ℕ) : Prop :=
  ∀ x y, Reach D x y → ¬ Reach D y x → pos x < pos y →
    ∃ g, Reach D g x ∧ Reach D x g ∧ pos y < pos g

/-- The invariant `H` of the depth-first search: `fin` finished vertices with positions `pos`. -/
def DfsH (D : Fin m → Fin n × Fin n) (fin : Finset (Fin n)) (pos : Fin n → ℕ) : Prop :=
  ∀ x ∈ fin, ∀ y, Reach D x y → ¬ Reach D y x → (y ∈ fin ∧ pos y < pos x) ∨
    ∃ g, Reach D g x ∧ Reach D x g ∧ (g ∉ fin ∨ (g ∈ fin ∧ y ∈ fin ∧ pos y < pos g))

end DirKECC1549.Asm

namespace DirKECC1549.Asm

end DirKECC1549.Asm



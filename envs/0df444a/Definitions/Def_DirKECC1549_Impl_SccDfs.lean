-- Prove2me | Definitions.Def_DirKECC1549_Impl_SccDfs
-- name    : DirKECC1549_Impl_SccDfs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-16T06:01:50.624447+00:00
-- url     : https://prove2.me/theorems/1eff0aa7-9c08-45d6-974a-1ffd1ec208d1
-- title:
--   Kosaraju's algorithm: the iterative depth-first search
-- statement:
--   The out-edge block start `ots`, the search state `DState` (stack, post-order, out-pointers) and the potential `Phi` bounding its running time.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model (p.25). Definitions of the verified word-RAM implementation of Algorithm 3.

import Definitions.Def_DirKECC1549_Impl_SccMath

set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main DirKECC1549.Main.CostAux

variable {n m : ℕ}

/-- `#{e : tail e < v}`: the start of the out-edges of `v` in the tail-sorted order. -/
def ots (D : Fin m → Fin n × Fin n) (v : ℕ) : ℕ := (univ.filter (fun e => ((D e).1 : ℕ) < v)).card

/-- The state of the iterative depth-first search: the stack `stk` (gray vertices, bottom first),
the post-order `po` of the finished vertices, and the next out-position `ptr v` of every gray `v`. -/
structure DState (D : Fin m → Fin n × Fin n) (σ : Equiv.Perm (Fin m)) (stk po : List (Fin n))
    (ptr : Fin n → ℕ) : Prop where
  nd : (stk ++ po).Nodup
  plo : ∀ v ∈ stk, ots D v ≤ ptr v
  phi : ∀ v ∈ stk, ptr v ≤ ots D (v + 1)
  pex : ∀ v ∈ stk, ∀ i : Fin m, ots D v ≤ i → (i : ℕ) < ptr v →
    (D (σ i)).2 ∈ stk ∨ (D (σ i)).2 ∈ po
  chain : ∀ i j (hi : i < stk.length) (hj : j < stk.length), i ≤ j → Reach D stk[i] stk[j]
  S2 : ∀ x ∈ po, ∀ e : Fin m, (D e).1 = x → (D e).2 ∈ stk ∨ (D e).2 ∈ po
  H : DfsH D po.toFinset (fun v => po.idxOf v)

/-- The out-degree in positions: `ots (v+1) - ots v`. -/
def odeg (D : Fin m → Fin n × Fin n) (v : Fin n) : ℕ := ots D (v + 1) - ots D v

/-- The potential of the search: it grows by at least one in every step. -/
def Phi (D : Fin m → Fin n × Fin n) (stk po : List (Fin n)) (ptr : Fin n → ℕ) : ℕ :=
  2 * po.length + stk.length + (∑ v ∈ po.toFinset, odeg D v) + ∑ v ∈ stk.toFinset, (ptr v - ots D v)

end DirKECC1549.Asm



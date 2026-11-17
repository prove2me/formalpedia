-- Prove2me | Definitions.Def_DirKECC1549_Impl_FlowBfs
-- name    : DirKECC1549_Impl_FlowBfs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-16T06:51:06.086633+00:00
-- url     : https://prove2.me/theorems/1737459e-0ee1-4808-b79f-ea8834a30e83
-- title:
--   Lemma 3 on the word-RAM: the residual search
-- statement:
--   The state `FState` of a breadth-first search in the residual graph (queue, parent edges, processed prefix) and the backward-walk predicate `BWalk` along parent edges.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model (p.25). Definitions of the verified word-RAM implementation of Algorithm 3.

import Definitions.Def_DirKECC1549_Impl_FlowMath

set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main DirKECC1549.Main.CostAux

variable {n m : ℕ}

/-- The search in the residual graph `H` from `z`: queue `q` (first `h` processed), parent edges
`par` (the parent edge of `q[i]`, `i > 0`, enters `q[i]` from an earlier queue vertex). -/
structure FState (H : Fin m → Fin n × Fin n) (z : Fin n) (q : List (Fin n)) (h : ℕ)
    (par : Fin n → Fin m) : Prop where
  nd : q.Nodup
  hd : ∃ hq : 0 < q.length, q[0] = z
  hle : h ≤ q.length
  parent : ∀ i (hi : i < q.length), 0 < i →
    (H (par q[i])).2 = q[i] ∧ ∃ j, ∃ hj : j < i, (H (par q[i])).1 = q[j]'(by omega)
  closed : ∀ i (hi : i < h), ∀ e, (H e).1 = q[i]'(by omega) → (H e).2 ∈ q

/-- The backward walk from `r`: from `x = q[i]`, the edges `t` collected so far form a trail to `r`,
each the parent edge of a later queue vertex. -/
def BWalk (H : Fin m → Fin n × Fin n) (q : List (Fin n)) (par : Fin n → Fin m) (r : Fin n) (i : ℕ)
    (hi : i < q.length) (t : List (Fin m)) : Prop :=
  IsTrail H q[i] t r ∧ ∀ e ∈ t, ∃ j, ∃ hj : j < q.length, i < j ∧ e = par q[j]

end DirKECC1549.Asm

namespace DirKECC1549.Asm

open DirKECC1549.Main DirKECC1549.Main.CostAux

variable {n m : ℕ}

end DirKECC1549.Asm



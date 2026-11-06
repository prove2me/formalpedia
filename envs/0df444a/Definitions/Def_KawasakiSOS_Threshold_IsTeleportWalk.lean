-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsTeleportWalk
-- name    : KawasakiSOS_Threshold_IsTeleportWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:00:48.205195+00:00
-- url     : https://prove2.me/theorems/9106f071-9242-4052-ba4f-be8d52a1cf77
-- title:
--   The walk realizing a teleport
-- statement:
--   Let $z(i)\ge1$ and $j\ne i$. The move $z\mapsto z-e_i+e_j$ is called a teleport. It is realized by moving the unit step by step along the shorter arc from $i$ to $j$. This predicate says that a list of states is that walk: the states $z-e_i+e_t$, where $t$ runs from $i$ to $j$ along an arc of length $L\le k/2$.
--
--   **Formalization Note** When $i$ and $j$ are antipodal, both arcs have length $k/2$ and either one is accepted.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 2.2, p. 6 (PDF p. 7)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_transfer
import Definitions.Def_KawasakiSOS_Threshold_stepSign

namespace KawasakiSOS.Threshold

/-- The walk of Lemma 2.2: for `z(i) ≥ 1` and `j ≠ i`, the list of states `z − e_i + e_t` for `t` running step by step along a shorter arc from `i` to `j`. Formalization Note: when `i` and `j` are antipodal both arcs are shortest, and either is accepted.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 2.2, p. 6 (PDF p. 7). -/
def IsTeleportWalk {n k : ℕ} [NeZero k] (z : Config n k) (i j : ZMod k)
    (l : List (Config n k)) : Prop :=
  1 ≤ z.1 i ∧ j ≠ i ∧ ∃ (s : Bool) (L : ℕ), 2 * L ≤ k ∧ j = i + (L : ZMod k) * stepSign s ∧
    l = (List.range (L + 1)).map fun t => transfer z i (i + (t : ZMod k) * stepSign s)

end KawasakiSOS.Threshold



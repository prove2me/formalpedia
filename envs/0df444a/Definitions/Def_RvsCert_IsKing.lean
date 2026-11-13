-- Prove2me | Definitions.Def_RvsCert_IsKing
-- name    : RvsCert_IsKing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:31.47911+00:00
-- url     : https://prove2.me/theorems/13bc6467-7d57-4b24-a1a5-b941725823f9
-- title:
--   King of a tournament
-- statement:
--   A vertex $v$ of a tournament is a **king** if it is reachable from every other vertex in at most two hops: for every $u\ne v$, either $v$ beats $u$, or $v$ beats some $w$ that beats $u$. With arcs from loser to winner this is the paper's definition; with arcs from winner to loser, as in Mande–Paraashar–Saurabh, it says every vertex is reachable from $v$ in at most two steps, which describes the same vertices.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 3, p.4 (after [MPS23])

import Mathlib
import Definitions.Def_RvsCert_beats

namespace RvsCert

/-- **King** (Section 3, p.4 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1, after [MPS23]: "a king is a vertex
reachable from every other vertex using at most 2 hops"). With arcs from loser to winner, `v` is
a king iff for every other vertex `u`, either `v` beats `u`, or `v` beats some `w` that beats
`u`. (In the orientation winner → loser of [MPS23] this is "every vertex is reachable from `v`
in at most 2 steps"; it is the same set of vertices.) -/
def IsKing {m : ℕ} (x : TPair m → Bool) (v : Fin m) : Prop :=
  ∀ u : Fin m, u ≠ v → beats x v u ∨ ∃ w : Fin m, beats x v w ∧ beats x w u

instance {m : ℕ} (x : TPair m → Bool) (v : Fin m) : Decidable (IsKing x v) := by
  unfold IsKing; infer_instance

end RvsCert



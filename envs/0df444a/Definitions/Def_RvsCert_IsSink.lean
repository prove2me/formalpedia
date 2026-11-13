-- Prove2me | Definitions.Def_RvsCert_IsSink
-- name    : RvsCert_IsSink
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:14.905106+00:00
-- url     : https://prove2.me/theorems/f55b19c4-64cd-471f-8284-64f6d78c1785
-- title:
--   Sink of a tournament
-- statement:
--   A vertex $s$ of a tournament is a **sink** if all $m-1$ arcs at $s$ point into it, that is (arcs pointing from loser to winner), $s$ beats every other vertex.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 3, p.4

import Mathlib
import Definitions.Def_RvsCert_beats

namespace RvsCert

/-- **Sink** (Section 3, p.4 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1: "a vertex for which all n − 1 incident arcs
are going into it rather than coming out"). With arcs from loser to winner, `s` is a sink iff
`s` beats every other vertex. -/
def IsSink {m : ℕ} (x : TPair m → Bool) (s : Fin m) : Prop :=
  ∀ u : Fin m, u ≠ s → beats x s u

instance {m : ℕ} (x : TPair m → Bool) (s : Fin m) : Decidable (IsSink x s) := by
  unfold IsSink; infer_instance

end RvsCert



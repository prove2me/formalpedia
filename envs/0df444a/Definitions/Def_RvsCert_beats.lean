-- Prove2me | Definitions.Def_RvsCert_beats
-- name    : RvsCert_beats
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:39:33.478194+00:00
-- url     : https://prove2.me/theorems/17488194-9577-4f07-b8b4-a92a11a4c01e
-- title:
--   $u$ beats $v$ in a tournament
-- statement:
--   For a tournament $x$ on $\{0,\dots,m-1\}$ and vertices $u\ne v$, **$u$ beats $v$** when the bit of the pair $\{u,v\}$ says so: for $u<v$, bit $1$ means $u$ beats $v$ and bit $0$ means $v$ beats $u$. No vertex beats itself, and of two distinct vertices exactly one beats the other. As in the paper, the arc between $u$ and $v$ points from the loser to the winner.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 3, p.4

import Mathlib
import Definitions.Def_RvsCert_TPair

namespace RvsCert

/-- **`u` beats `v` in the tournament `x`** (Section 3, p.4 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1: "we
intuitively say that p beats q (and hence orient the arc so that it goes from q to p)").

**Formalization Note.** Convention: for `u < v` the bit `x ⟨(u, v), _⟩ = true` means `u` beats
`v`, and `false` means `v` beats `u`. No vertex beats itself, and for `u ≠ v` exactly one of
`beats x u v`, `beats x v u` holds. The arc of the paper goes from the loser to the winner. -/
def beats {m : ℕ} (x : TPair m → Bool) (u v : Fin m) : Prop :=
  if h : u < v then x ⟨(u, v), h⟩ = true
  else if h' : v < u then x ⟨(v, u), h'⟩ = false else False

instance {m : ℕ} (x : TPair m → Bool) (u v : Fin m) : Decidable (beats x u v) := by
  unfold beats; infer_instance

end RvsCert



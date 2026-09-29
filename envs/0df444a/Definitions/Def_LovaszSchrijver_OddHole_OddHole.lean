-- Prove2me | Definitions.Def_LovaszSchrijver_OddHole_OddHole
-- name    : LovaszSchrijver_OddHole_OddHole
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:45:48.296129+00:00
-- url     : https://prove2.me/theorems/eaabde8b-2c0f-44d6-b17a-0e3b322c8dc1
-- title:
--   Odd holes: vertex sets inducing a chordless odd cycle (Section 2.a)
-- statement:
--   A set $C$ of nodes of a graph $G$ **induces a chordless odd cycle** (an odd hole, p. 175) if $|C| = m$ is odd, $m \ge 3$, and the nodes of $C$ can be listed as $c_0, c_1, \dots, c_{m-1}$ so that $c_s$ and $c_t$ are adjacent in $G$ exactly when $t \equiv s \pm 1 \pmod m$. The paper's odd hole constraint for such $C$ is
--   $$\sum_{i \in C} x_i \le \tfrac12(|C| - 1).$$
--
--   **Formalization Note** Triangles ($m = 3$) are odd holes under this definition; they must be, since the triangle constraint $x_1 + x_2 + x_3 \le 1$ is one of the constraints in Theorem 2.3. Chords are excluded, following the definition on p. 175; the page's remark that the inequality also holds for odd cycles with chords, where it is implied by other constraints, is not part of the definition.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 175, Section 2.a, (4)

import Mathlib

namespace LovaszSchrijver.OddHole

/-- `C` induces a chordless odd cycle in `G` (an odd hole, p. 175): for some odd `m ≥ 3`
there is a bijection `f : Fin m ≃ C` under which two vertices of `C` are adjacent in `G`
exactly when their indices are consecutive modulo `m`. Triangles (`m = 3`) are included. -/
def IsOddHole {V : Type} (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ ∃ f : Fin m ≃ C, ∀ s t : Fin m,
    G.Adj (f s).1 (f t).1 ↔ (t.val = (s.val + 1) % m ∨ s.val = (t.val + 1) % m)

end LovaszSchrijver.OddHole



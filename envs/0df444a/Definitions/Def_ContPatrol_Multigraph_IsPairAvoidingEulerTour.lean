-- Prove2me | Definitions.Def_ContPatrol_Multigraph_IsPairAvoidingEulerTour
-- name    : ContPatrol_Multigraph_IsPairAvoidingEulerTour
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:41.966879+00:00
-- url     : https://prove2.me/theorems/e46ba901-77ee-4f28-9a9d-efa52d126342
-- title:
--   Lemma 3: passages, pairings, and pair-avoiding Eulerian tours
-- statement:
--   A **passage** at a node $x$ is a pair $(x,a)$ with $a$ an arc incident to $x$; a node of degree $d$ has $d$ passages (a loop contributes two). A **pairing** identifies the passages at every node in pairs.
--
--   An **Eulerian tour** is a closed walk traversing every edge exactly once. It **avoids paired passages** if it never enters and leaves a node via two paired passages (condition (2) of the paper).
--
--   These are the notions of Lemma 3, the refinement of Euler's theorem behind Theorem 3.
--
--   **Formalization Note** A passage $(x,a)$ is encoded as the dart along $a$ leaving $x$; a pairing is a fixed-point-free involution on darts that keeps each dart at its node. The walk enters the head of a dart $d$ through the passage of the reverse of $d$, and leaves through the next dart. A vertex of degree $2$ is a regular point, not a node, so condition (2) is imposed only at vertices of degree other than $2$.
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, §4, p.11, Lemma 3 and display (2)

import Mathlib
import Definitions.Def_ContPatrol_Multigraph

namespace ContPatrol

namespace Multigraph

variable {V E : Type}

/-- **Pairings of passages (Lemma 3).**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, §4, p.11:
"Formally, a passage at a node x is a pair (x, a), where a is an arc incident to x. So a node of
degree d has d passages and every arc is part of two passages." Lemma 3: "at every node the
passages are identified in pairs (they are “paired”)."

A passage is encoded as the dart leaving its node along the arc: the passage `(x, a)` is the dart
`d` with `d.1 = a` and `tail d = x` (a loop gives two passages at its vertex, as it should). A
pairing is a fixed-point-free involution `σ` on darts that keeps every dart at its node. -/
def IsPassagePairing (G : Multigraph V E) (σ : E × Bool → E × Bool) : Prop :=
  (∀ d, σ (σ d) = d) ∧ (∀ d, σ d ≠ d) ∧ ∀ d, G.tail (σ d) = G.tail d

/-- **Eulerian tours avoiding paired passages, condition (2) of Lemma 3.**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, Lemma 3,
p.11: "an Eulerian tour S of Q satisfying S never enters and leaves a node via paired passages.
(2)"

`G.IsPairAvoidingEulerTour σ w`: `w` is a closed dart walk using every edge exactly once, and at
every node it passes (cyclically, including the wrap-around) the passage it enters by and the
passage it leaves by are not paired. The walk enters `head w[i]` through the passage
`rev w[i]` and leaves it through the passage `w[i+1]`.

**Formalization Note.** A vertex of degree 2 is a regular point of Q, not a node (p.5), so the
condition is imposed only at vertices of degree other than 2. -/
def IsPairAvoidingEulerTour [Fintype E] [DecidableEq V] [DecidableEq E] (G : Multigraph V E)
    (σ : E × Bool → E × Bool) (w : List (E × Bool)) : Prop :=
  G.IsClosedDartWalk w ∧ (∀ e : E, w.countP (fun d => d.1 = e) = 1) ∧
    ∀ (i : ℕ) (hi : i < w.length), G.deg (G.head w[i]) ≠ 2 →
      σ (rev w[i]) ≠ w[(i + 1) % w.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi))

end Multigraph

end ContPatrol



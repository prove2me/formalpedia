-- Prove2me | Definitions.Def_PebbleMotion_Trees_Isthmus
-- name    : PebbleMotion_Trees_Isthmus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:37:29.993502+00:00
-- url     : https://prove2.me/theorems/9ad1633f-2ab6-4244-805e-ea2a1f95d86b
-- title:
--   Cut vertices, isthmuses, the maximum isthmus size $k(G)$, inner vertices, cycle graphs
-- statement:
--   Let $G$ be a graph. A **cut vertex** is a vertex $v$ such that some two vertices $a,b\ne v$ joined by a walk of $G$ have every walk from $a$ to $b$ passing through $v$.
--
--   A path $I=v_1\cdots v_d$ ($d\ge1$ distinct vertices, consecutive ones adjacent) is an **isthmus** of $G$ if (1) every edge $v_iv_{i+1}$ is a bridge of $G$, (2) every $v_i$ is a cut vertex of $G$, and (3) $\deg_G(v_i)=2$ for $1<i<d$. A $d$-isthmus has $d$ vertices; a single cut vertex is a $1$-isthmus.
--
--   The **maximum isthmus size** is $k(G)=\max\{|V(I)| : I \text{ an isthmus of } G\}$ if $G$ has an isthmus, and $k(G)=1$ otherwise. In Lean it is $\max(1,\sup S)$ with $S$ the set of isthmus sizes: for a finite graph $S$ is bounded by $|V(G)|$, and $\sup\emptyset=0$ gives the value $1$.
--
--   The **inner vertices** of $I=v_1\cdots v_d$ are $v_2,\dots,v_{d-1}$. $G$ **is a cycle** if it is connected and every vertex has exactly two neighbours (for a finite graph: the cycle $C_N$, $N\ge3$).
-- source:
--   Nakamigawa and Sakuma, Structural Origins of Cubic Complexity in Pebble Motion, arXiv:2503.20550 (held revision dated 2026-11-03), §2.1 (isthmus, k(G)) and Theorem A, p.7–8, PDF SHA256 efd330453039630e97e2ef1029ef0b2b3ac5a16bd700a2c5fad226582870f412

import Mathlib

set_option autoImplicit false

namespace PebbleMotion.Trees

variable {V : Type*}

/-- A **cut vertex** of a graph `G` (Nakamigawa–Sakuma, *Structural Origins of Cubic Complexity in
Pebble Motion*, §2.1, p.7): a vertex `v` whose removal separates two vertices that are connected
in `G`, i.e. there are vertices `a, b ≠ v`, joined by a walk of `G`, such that every walk of `G`
from `a` to `b` passes through `v`. -/
def IsCutVertex (G : SimpleGraph V) (v : V) : Prop :=
  ∃ a b : V, a ≠ v ∧ b ≠ v ∧ G.Reachable a b ∧ ∀ p : G.Walk a b, v ∈ p.support

/-- An **isthmus** (p.7): a path `I = v₁ ⋯ v_d` of `G` (`d ≥ 1` distinct vertices, consecutive
ones adjacent) such that
1. every edge `v_i v_{i+1}` of `I` is a bridge of `G`;
2. every vertex of `I` is a cut vertex of `G`;
3. `deg_G(v_i) = 2` for `1 < i < d`.

The path is the list `I = [v₁, …, v_d]`; its size `|V(I)|` is `I.length`. A `d`-isthmus is an
isthmus with `I.length = d`. Degrees are `(G.neighborSet v).ncard`. -/
def IsIsthmus (G : SimpleGraph V) (I : List V) : Prop :=
  I ≠ [] ∧ I.Nodup ∧
  (∀ (i : ℕ) (h : i + 1 < I.length),
      G.Adj (I[i]'(by omega)) (I[i + 1]'h) ∧ G.IsBridge s(I[i]'(by omega), I[i + 1]'h)) ∧
  (∀ v ∈ I, IsCutVertex G v) ∧
  (∀ (i : ℕ) (h : i + 1 < I.length), 0 < i → (G.neighborSet (I[i]'(by omega))).ncard = 2)

/-- The **maximum isthmus size** `k(G)` (p.7): the largest number of vertices of an isthmus of
`G` if `G` has an isthmus, and `1` otherwise. The set of isthmus sizes of a finite graph is
bounded by the number of vertices (an isthmus is a list without repetitions), so the `sSup` is
its maximum; when there is no isthmus the set is empty, `sSup ∅ = 0`, and the value is `1`. -/
noncomputable def maxIsthmusSize (G : SimpleGraph V) : ℕ :=
  max 1 (sSup {d : ℕ | ∃ I : List V, IsIsthmus G I ∧ I.length = d})

/-- The **inner vertices** of a path `I = v₁ ⋯ v_d`: the list `v₂ ⋯ v_{d-1}` (empty when
`d ≤ 2`). -/
def innerVertices (I : List V) : List V := (I.drop 1).dropLast

/-- `G` **is a cycle** (the case excluded in Theorem A, p.8): `G` is connected and every vertex has
exactly two neighbours. For a finite graph this is exactly the cycle graph `C_N` (`N ≥ 3`). -/
def IsCycleGraph (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ v : V, (G.neighborSet v).ncard = 2

end PebbleMotion.Trees



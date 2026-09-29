-- Prove2me | Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
-- name    : EdmondsKarp_ShortestPath_Augmentation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:09:46.553141+00:00
-- url     : https://prove2.me/theorems/07885c02-d607-4787-a868-d0fc79454748
-- title:
--   Residual network $N^f$, augmenting paths, bottleneck arcs and the Edmonds–Karp augmentation
-- statement:
--   Let $f$ be a flow in a network $N$ with arc set $A$ (return arc excluded), capacities $c$, source $s$ and sink $t$.
--
--   **Residual network.** The network $N^f$ has the same nodes as $N$, and $(u,v)$ is an arc of $N^f$ if and only if either $(u,v) \in A$ and $c(u,v) - f(u,v) > 0$, or $(v,u) \in A$ and $f(v,u) > 0$.
--
--   **Directed paths and augmenting paths.** A directed path from $u$ to $v$ in $N^f$ is a sequence of *distinct* nodes $u = u_1, u_2, \dots, u_p = v$ such that each consecutive pair $(u_i,u_{i+1})$ is an arc of $N^f$; its length is its number of arcs, $p-1$. An **augmenting path** relative to $f$ is a directed path from $s$ to $t$ in $N^f$; this is the one-one correspondence between augmenting paths in $N$ and directed $s$–$t$ paths in $N^f$.
--
--   **The numbers $\varepsilon_i$.** For a step $(u_i,u_{i+1})$ of an augmenting path:
--
--   1. Case (a): if $(u_i,u_{i+1}) \in A$ and $(u_{i+1},u_i) \notin A$, then $\varepsilon_i = c(u_i,u_{i+1}) - f(u_i,u_{i+1})$;
--   2. Case (b): if $(u_i,u_{i+1}) \notin A$ and $(u_{i+1},u_i) \in A$, then $\varepsilon_i = f(u_{i+1},u_i)$;
--   3. Case (c): if $(u_i,u_{i+1}) \in A$ and $(u_{i+1},u_i) \in A$, then $\varepsilon_i = c(u_i,u_{i+1}) - f(u_i,u_{i+1}) + f(u_{i+1},u_i)$.
--
--   Let $\varepsilon = \min_i \varepsilon_i$. A step $(u_i,u_{i+1})$ with $\varepsilon_i = \varepsilon$ is a **bottleneck arc** relative to $P$ and $f$.
--
--   **Augmentation.** The flow $f'$ is obtained from $f$ by increasing $f$ by $\varepsilon$ on the return arc $(t,s)$; in Case (a), increasing the flow on $(u_i,u_{i+1})$ by $\varepsilon$; in Case (b), decreasing the flow on $(u_{i+1},u_i)$ by $\varepsilon$; in Case (c), increasing the flow on $(u_i,u_{i+1})$ by $\min(\varepsilon,\, c(u_i,u_{i+1}) - f(u_i,u_{i+1}))$ and decreasing the flow on $(u_{i+1},u_i)$ by $\max(0,\, \varepsilon - c(u_i,u_{i+1}) + f(u_i,u_{i+1}))$. All other arcs keep their flow.
--
--   Case (c) is the paper's own rule for opposite arcs and differs from the original Ford–Fulkerson rule; the results of the mission concern this rule.
--
--   **Formalization Note** Paths are lists of nodes (`List V`) with `Nodup`, first element `s`, last element `t`, and every consecutive pair (`pathArcs P = P.zip P.tail`) an arc of $N^f$; in particular the return arc is never used. Case (b) is stated with $(u_i,u_{i+1}) \notin A$: the printed page repeats the hypothesis of Case (c), an evident misprint corrected by the paper's own description of $N^f$ (p. 251) and of $e(u,v)$ (p. 253). `pathEps` is the minimum of the list of the $\varepsilon_i$, with default `0` for a path without arcs, which never occurs for an augmenting path since $s \ne t$. `augment` changes only the return arc and arcs of `A`.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 249, §1.1 (paths, augmenting paths, Cases (a)–(c), bottleneck arcs, augmentation) and p. 251, §1.2 (network N^f, directed path, bottleneck arc of P^f)

import Mathlib
import Definitions.Def_EdmondsKarp_ShortestPath_Network

namespace EdmondsKarp.ShortestPath

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The arcs of the residual network `N^f` (§1.2, p. 251): `(u, v)` is an arc of `N^f` iff
`(u, v) ∈ A` and `c(u, v) − f(u, v) > 0`, or `(v, u) ∈ A` and `f(v, u) > 0`. -/
def ResArc (N : Network V) (f : V → V → ℝ) (u v : V) : Prop :=
  ((u, v) ∈ N.A ∧ 0 < N.c u v - f u v) ∨ ((v, u) ∈ N.A ∧ 0 < f v u)

/-- The consecutive pairs `(u_i, u_{i+1})` of a node sequence `u_1, …, u_p`. -/
def pathArcs (P : List V) : List (V × V) := P.zip P.tail

/-- A directed path from `u` to `v` in `N^f` (pp. 249, 251): a sequence of distinct nodes starting at
`u`, ending at `v`, each consecutive pair of which is an arc of `N^f`. Its length is the number of
arcs, `(pathArcs P).length`. -/
def IsDirPath (N : Network V) (f : V → V → ℝ) (u v : V) (P : List V) : Prop :=
  P.Nodup ∧ P.head? = some u ∧ P.getLast? = some v ∧ ∀ e ∈ pathArcs P, ResArc N f e.1 e.2

/-- An augmenting path relative to `f` (p. 249), encoded through the one-one correspondence of p. 251 as
a directed path from `s` to `t` in `N^f`. -/
def IsAugPath (N : Network V) (f : V → V → ℝ) (P : List V) : Prop :=
  IsDirPath N f N.s N.t P

/-- The number `ε_i` attached to a step `(u, v) = (u_i, u_{i+1})` of an augmenting path (p. 249,
Case (b) corrected to `(u, v) ∉ A`, `(v, u) ∈ A`):
(a) `(u,v) ∈ A`, `(v,u) ∉ A`: `c(u,v) − f(u,v)`; (b) `(u,v) ∉ A`, `(v,u) ∈ A`: `f(v,u)`;
(c) both in `A`: `c(u,v) − f(u,v) + f(v,u)`. (If neither is in `A` the value is irrelevant.) -/
def stepEps (N : Network V) (f : V → V → ℝ) (u v : V) : ℝ :=
  if (u, v) ∈ N.A then
    (if (v, u) ∈ N.A then N.c u v - f u v + f v u else N.c u v - f u v)
  else f v u

/-- `ε = min ε_i` over the steps of the path `P` (p. 249). (The default `0` for a path without arcs
never arises for an augmenting path, which has at least one arc since `s ≠ t`.) -/
def pathEps (N : Network V) (f : V → V → ℝ) (P : List V) : ℝ :=
  (((pathArcs P).map (fun e => stepEps N f e.1 e.2)).min?).getD 0

/-- `(u, v)` is a bottleneck arc relative to `P` and `f` (pp. 249, 251): a step `(u_i, u_{i+1})` of `P`
(an arc of `N^f`) with `ε_i = ε`. -/
def IsBottleneck (N : Network V) (f : V → V → ℝ) (P : List V) (u v : V) : Prop :=
  (u, v) ∈ pathArcs P ∧ stepEps N f u v = pathEps N f P

/-- Increase of the flow on the arc `(x, y) ∈ A` in the augmentation along `P` (p. 249): `ε` in Case (a)
and `min(ε, c(x,y) − f(x,y))` in Case (c), when `(x, y)` is a step of `P`; otherwise `0`. -/
def augIncrease (N : Network V) (f : V → V → ℝ) (P : List V) (x y : V) : ℝ :=
  if (x, y) ∈ pathArcs P then
    (if (y, x) ∈ N.A then min (pathEps N f P) (N.c x y - f x y) else pathEps N f P)
  else 0

/-- Decrease of the flow on the arc `(x, y) ∈ A` in the augmentation along `P` (p. 249): when `(y, x)`
is a step of `P`, `ε` in Case (b) and `max(0, ε − c(y,x) + f(y,x))` in Case (c); otherwise `0`. -/
def augDecrease (N : Network V) (f : V → V → ℝ) (P : List V) (x y : V) : ℝ :=
  if (y, x) ∈ pathArcs P then
    (if (y, x) ∈ N.A then max 0 (pathEps N f P - N.c y x + f y x) else pathEps N f P)
  else 0

/-- The flow `f'` obtained from `f` by augmentation along `P` (p. 249): the return arc gains `ε`, each
arc of `A` changes by its increase minus its decrease; values off the arcs of `N` are left unchanged. -/
def augment (N : Network V) (f : V → V → ℝ) (P : List V) : V → V → ℝ :=
  fun x y =>
    if x = N.t ∧ y = N.s then f x y + pathEps N f P
    else if (x, y) ∈ N.A then f x y + augIncrease N f P x y - augDecrease N f P x y
    else f x y

end EdmondsKarp.ShortestPath



-- Prove2me | Definitions.Def_GraphonCheeger_stepGraphon
-- name    : GraphonCheeger_stepGraphon
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:39:40.185202+00:00
-- url     : https://prove2.me/theorems/88cbb714-fffa-4a8d-8a11-0c35f6b3b353
-- title:
--   The continuous graphon $W_G$ on $[0,1]$ and the atomic graphon $W'_G$ of a finite graph
-- statement:
--   Let $G$ be a graph on the vertex set $\{0,\dots,n-1\}$, $n\ge1$.
--
--   1. The **atomic graphon** $W'_G$ lives on $V(G)$ with the uniform probability measure and is the adjacency matrix: $W'_G(u,v)=1$ if $u\sim v$ and $0$ otherwise.
--   2. The **continuous graphon** $W_G$ lives on $[0,1]$ with Lebesgue measure. Split $[0,1]$ into the $n$ intervals $I_v=[v/n,(v+1)/n)$, the last one closed at $1$, and set $W_G(x,y)=1$ if the vertices $u,v$ with $x\in I_u$, $y\in I_v$ are adjacent, and $W_G(x,y)=0$ otherwise.
--
--   $W_G$ is the blow-up of $W'_G$ (each vertex becomes an interval of length $1/n$); it is the graphon through which a sequence of finite graphs is compared with a limit graphon.
--
--   **Formalization Note** The cell of $x\in[0,1]$ is $\min(\lfloor nx\rfloor,n-1)$. Any other split of $[0,1]$ into $n$ intervals of equal length agrees with this one off a finite set, so it gives the same graphon up to a null set. For $n=0$, where the construction is undefined, $W_G$ is the junk value $0$. Graphs have vertex set `Fin n`.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Example 2.4, p.7

import Mathlib

open MeasureTheory

namespace GraphonCheeger

/-!
# The continuous (step) graphon `W_G` and the atomic graphon `W′_G` of a finite graph

Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…), Example 2.4, p.7.

**Formalization Note.**
* Graphs have vertex set `Fin n` (every finite graph is isomorphic to one).
* `W_G` lives on `unitInterval = [0, 1]` with Lebesgue measure (`volume`). The cell map
  `cell n x = min ⌊n·x⌋ (n − 1)` sends `x ∈ [v/n, (v+1)/n)` to `v` and the point `1` to the last
  vertex `n − 1`, so the cells `I_v` are intervals of length `1/n`; any other split of `[0, 1]`
  into `n` intervals of equal length agrees with this one off a finite set, so the step graphon
  is the same up to a null set. For `n = 0` (where the paper's construction is undefined) the
  value is the junk `0`.
* `W′_G` lives on `Fin n` with the uniform probability measure `atomicMeasure n`.
-/

/-- `min k (n − 1)` as an element of `Fin n` (for `n ≠ 0`). -/
def clampFin (n : ℕ) [NeZero n] (k : ℕ) : Fin n :=
  ⟨min k (n - 1), Nat.lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne n)) Nat.one_pos)⟩

/-- The cell map `[0, 1] → Fin n`, `x ↦ min ⌊n·x⌋ (n − 1)`: the cell of `v` is
`I_v = [v/n, (v+1)/n)`, and the last cell also contains `1`. -/
noncomputable def cell (n : ℕ) [NeZero n] (x : unitInterval) : Fin n :=
  clampFin n ⌊(n : ℝ) * (x : ℝ)⌋₊

/-- The **continuous graphon** `W_G` of a graph `G` on `Fin n` (Example 2.4, p.7):
`W_G(x, y) = 1` if the vertices of the cells containing `x` and `y` are adjacent, else `0`. -/
noncomputable def stepGraphon {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x y : unitInterval) : ℝ :=
  if h : 0 < n then
    haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp h⟩
    if G.Adj (cell n x) (cell n y) then 1 else 0
  else 0

/-- The uniform probability measure on `Fin n` (the vertex set of `W′_G`). -/
noncomputable def atomicMeasure (n : ℕ) : Measure (Fin n) :=
  ProbabilityTheory.uniformOn (Set.univ : Set (Fin n))

/-- The **atomic graphon** `W′_G` of a graph `G` on `Fin n` (Example 2.4, p.7): the adjacency
matrix, `W′_G(u, v) = 1` if `u ∼ v` and `0` otherwise, on `Fin n` with `atomicMeasure n`. -/
def atomicGraphon {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) : ℝ :=
  if G.Adj u v then 1 else 0

end GraphonCheeger



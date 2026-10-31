-- Prove2me | Definitions.Def_MultiwayCut_Instance
-- name    : MultiwayCut_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:14.580977+00:00
-- url     : https://prove2.me/theorems/0514f32d-7f27-4ce3-a713-ef2800c47ee0
-- title:
--   Multiway Cut instances, feasible labelings, cut weight and the simplex relaxation
-- statement:
--   This module fixes the Multiway Cut problem and its geometric (simplex) relaxation.
--
--   1. **Instance** (§2, p.3). A finite set of edges $E$ between vertices of $V$, written as ordered pairs $(u,v)$, a weight $w_e\ge0$ for every $e\in E$, and $k$ distinct terminals $t_1,\dots,t_k\in V$.
--   2. **Feasible labeling.** An assignment $g:V\to\{1,\dots,k\}$ with $g(t_i)=i$ for every $i$. An edge $(u,v)$ is **cut** when $g(u)\ne g(v)$, and the **weight of the cut** is
--   $$\mathrm{cut}(g)=\sum_{e=(u,v)\in E,\ g(u)\ne g(v)} w_e .$$
--   3. **Simplex relaxation** (§2.1, p.3). Let $\Delta_k=\{x\in\mathbb R^k: x\ge0,\ \sum_i x_i=1\}$ and let $e_i$ be its $i$-th vertex. A **feasible embedding** maps every vertex $u$ to a point $\mathbf u\in\Delta_k$ with $\mathbf t_i=e_i$. Its **objective** is
--   $$\sum_{e=(u,v)\in E} w_e\cdot\tfrac12\,\|\mathbf u-\mathbf v\|_1 ,$$
--   and an **optimal** embedding minimizes it over all feasible embeddings.
--
--   Every guarantee of the mission compares the expected cut of a rounding algorithm with this objective.
--
--   **Formalization Note** Terminals and coordinates are indexed by `Fin k` from $0$, so $t_i$ is `t (i-1)` and $e_i$ is `Pi.single (i-1) 1`; $\Delta_k$ is Mathlib's `stdSimplex ℝ (Fin k)`. The edge set is a `Finset (V × V)`: an undirected graph lists each edge once, and parallel copies or loops, if listed, are counted as written. Weights are a function on $V\times V$, nonnegative on $E$.
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, §2 and §2.1, p.3 (the Multiway Cut problem; the simplex relaxation)

import Mathlib

namespace MultiwayCut

/-- **Multiway Cut instance**, Buchbinder, Schwartz & Weizman, *Simplex Transformations and the
Multiway Cut Problem*, manuscript of Nov. 1, 2016, §2, p.3: an edge weighted graph `G = (V, E)`,
`w : E → ℝ⁺`, and `k` terminals `T = {t₁, …, t_k} ⊆ V`.

**Formalization Note.** Edges are a finite set `E` of ordered pairs `(u, v)` of vertices; a
graph's undirected edge set is the special case listing each edge once (both orientations, a
parallel copy or a loop are allowed and simply counted as written). The weight `w` is a function
on `V × V`, nonnegative on `E`. The paper's terminal `tᵢ` (`i = 1, …, k`) is `t (i - 1)`:
terminals are indexed by `Fin k` from `0`. The terminals are distinct (`t` injective). -/
structure Instance (V : Type*) (k : ℕ) where
  /-- the edges, as ordered pairs of endpoints -/
  E : Finset (V × V)
  /-- the edge weights -/
  w : V × V → ℝ
  w_nonneg : ∀ e ∈ E, 0 ≤ w e
  /-- the terminals `t₀, …, t_{k-1}` -/
  t : Fin k → V
  t_injective : Function.Injective t

variable {V : Type*} {k : ℕ}

/-- **Feasible labeling**, manuscript of Nov. 1, 2016, §2, p.3: an assignment
`g : V → {1, …, k}` with `g(tᵢ) = i` for every `i` (0-based: `g (t i) = i`). -/
def IsFeasibleLabeling (I : Instance V k) (g : V → Fin k) : Prop :=
  ∀ i : Fin k, g (I.t i) = i

/-- **Weight of the cut of a labeling**, manuscript of Nov. 1, 2016, §2, p.3: an edge `(u, v)`
is cut (belongs to `X`) iff `g(u) ≠ g(v)`; the cost is the total weight of the cut edges. -/
def cutWeight (I : Instance V k) (g : V → Fin k) : ℝ :=
  ∑ e ∈ I.E with g e.1 ≠ g e.2, I.w e

/-- Half the `ℓ₁` distance, `½ ‖u − v‖₁`, the length of an edge in the simplex relaxation
(manuscript of Nov. 1, 2016, §2.1, p.3). -/
noncomputable def halfL1 (u v : Fin k → ℝ) : ℝ :=
  1 / 2 * ∑ ℓ, |u ℓ - v ℓ|

/-- **Feasible point of the simplex relaxation**, manuscript of Nov. 1, 2016, §2.1, p.3: every
vertex is embedded into the simplex `Δ_k = {x ∈ ℝᵏ : x ≥ 0, Σᵢ xᵢ = 1}` and each terminal `tᵢ`
is embedded to the vertex `eᵢ`.

**Formalization Note.** `Δ_k` is Mathlib's `stdSimplex ℝ (Fin k)` and `eᵢ` is
`Pi.single i 1` (0-based). -/
def IsFeasibleEmbedding (I : Instance V k) (x : V → Fin k → ℝ) : Prop :=
  (∀ v, x v ∈ stdSimplex ℝ (Fin k)) ∧ ∀ i : Fin k, x (I.t i) = Pi.single i 1

/-- **Objective of the simplex relaxation**, manuscript of Nov. 1, 2016, §2.1, p.3:
`Σ_{e=(u,v)∈E} w_e · ½ ‖u − v‖₁`. -/
noncomputable def relaxValue (I : Instance V k) (x : V → Fin k → ℝ) : ℝ :=
  ∑ e ∈ I.E, I.w e * halfL1 (x e.1) (x e.2)

/-- An **optimal solution of the simplex relaxation** (§2.1, p.3): a feasible embedding whose
objective is at most that of every feasible embedding. -/
def IsRelaxOptimal (I : Instance V k) (x : V → Fin k → ℝ) : Prop :=
  IsFeasibleEmbedding I x ∧ ∀ y, IsFeasibleEmbedding I y → relaxValue I x ≤ relaxValue I y

end MultiwayCut



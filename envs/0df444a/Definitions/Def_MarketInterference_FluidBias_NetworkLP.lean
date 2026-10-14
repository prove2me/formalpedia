-- Prove2me | Definitions.Def_MarketInterference_FluidBias_NetworkLP
-- name    : MarketInterference_FluidBias_NetworkLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:17:45.894335+00:00
-- url     : https://prove2.me/theorems/13d80d17-7147-4660-a245-34c6ef3cdd3f
-- title:
--   pp. 7, 10 — the capacitated matching network, the network-flow LP Φ_τ(d, s) of (2) and its dual (5)
-- statement:
--   A **matching network** is a finite directed graph $\mathcal G=(\mathcal U,\mathcal A)$ whose nodes are split into demand nodes $u^d_1,\dots,u^d_{n_d}$ (one per demand type, sinks with only incoming arcs), supply nodes $u^s_1,\dots,u^s_{n_s}$ (one per supply type, sources with only outgoing arcs) and intermediate nodes $\mathcal U_*$. Each arc $(u,w)\in\mathcal A$ carries a value $v_{u,w}\in\mathbb R$ per unit of flow and a capacity $k_{u,w}\ge 0$.
--
--   For a scale $\tau$, a demand vector $d$ and a supply vector $s$, the platform's matching problem is the linear program (2):
--   $$
--   \Phi_\tau(d,s)=\max\sum_{(u,w)\in\mathcal A}v_{u,w}x_{u,w}
--   $$
--   subject to (2b) $\sum_{w:(w,u^d_i)\in\mathcal A}x_{w,u^d_i}\le d_i$ for every demand type $i$; (2c) $\sum_{w:(u^s_j,w)\in\mathcal A}x_{u^s_j,w}\le s_j$ for every supply type $j$; (2d) inflow equals outflow at every intermediate node; and (2e) $0\le x_{u,w}\le\tau k_{u,w}$ on every arc. For $\tau=1$ one writes $\Phi(d,s)$.
--
--   The dual (5) has variables $a_i\ge 0$ (demand), $b_j\ge 0$ (supply), $\xi_{u,w}\ge 0$ (capacity) and free potentials $m_u$ on the intermediate nodes. It minimises
--   $$
--   \sum_{i=1}^{n_d}a_id_i+\sum_{j=1}^{n_s}b_js_j+\sum_{(u,w)\in\mathcal A}\xi_{u,w}k_{u,w}\tau
--   $$
--   subject to one constraint per arc: $b_j+a_i+\xi\ge v$ on supply→demand arcs (5b), $b_j-m_w+\xi\ge v$ on supply→intermediate arcs (5c), $m_w+a_i+\xi\ge v$ on intermediate→demand arcs (5d) and $m_u-m_w+\xi\ge v$ on intermediate→intermediate arcs (5e). The variable $a_i$ is the shadow price of an additional unit of demand of type $i$.
--
--   These objects are the deterministic core of the paper: the fluid-limit value $\Phi(\lambda,\pi)$ of the matching market and the shadow prices used by the shadow-price estimator.
--
--   **Formalization Note.** Demand types are `Fin nd` (Lean index $i$ is the paper's type $i+1$), supply types `Fin ns`, intermediate nodes a finite type `I`, arcs a finite type `E`; an arc's tail is `Sum.inl j` (supply node) or `Sum.inr u` (intermediate), its head `Sum.inl i` (demand node) or `Sum.inr w`, so the sink/source convention holds by construction, and the bipartite case is `I = Empty`. Parallel arcs are allowed. `Phi` is the supremum of the objective over the feasible set; for $\tau,d,s\ge 0$ the feasible set contains $0$ and lies in the box $[0,\tau k]$, so the supremum is attained, while on an infeasible argument Lean returns $0$ (no statement of this mission evaluates `Phi` there). The four dual constraints are written uniformly as (tail potential) + (head potential) + $\xi_e\ge v_e$, with tail potential $b_j$ or $m_u$ and head potential $a_i$ or $-m_w$. `IsOptimal` and `IsOptimalDual` mean feasible and optimal for (2) and (5) respectively; strong duality is not built in.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 7, (2a)–(2e); p. 10, (5a)–(5h)

import Mathlib

namespace MarketInterference.FluidBias

/-- A capacitated matching network (Bright–Delarue–Lobel, p. 7). Demand types are `Fin nd`
(Lean index `i` is the paper's type `i + 1`), supply types `Fin ns`, intermediate nodes `I`,
arcs `E`. An arc runs from a supply node `u^s_j` (`Sum.inl j`) or an intermediate node
(`Sum.inr u`) to a demand node `u^d_i` (`Sum.inl i`) or an intermediate node (`Sum.inr w`), so
demand nodes only have incoming arcs and supply nodes only outgoing arcs. Each arc carries a
value `v` and a capacity `k ≥ 0`. Parallel arcs are allowed. -/
structure Network (nd ns : ℕ) (I E : Type) where
  /-- tail of an arc: a supply node or an intermediate node -/
  tail : E → Fin ns ⊕ I
  /-- head of an arc: a demand node or an intermediate node -/
  head : E → Fin nd ⊕ I
  /-- value `v_{u,w}` of one unit of flow on the arc -/
  v : E → ℝ
  /-- capacity `k_{u,w}` of the arc (scaled to `τ k_{u,w}` in `Φ_τ`) -/
  k : E → ℝ
  k_nonneg : ∀ e, 0 ≤ k e

variable {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]

/-- Feasibility of an arc flow `x` for the LP (2) with scale `τ`, demand vector `d` and supply
vector `s`: (2e) `0 ≤ x ≤ τ k`; (2b) inflow at each demand node `≤ d_i`; (2c) outflow at each
supply node `≤ s_j`; (2d) flow balance at each intermediate node. -/
def Feasible (N : Network nd ns I E) (τ : ℝ) (d : Fin nd → ℝ) (s : Fin ns → ℝ) (x : E → ℝ) :
    Prop :=
  (∀ e, 0 ≤ x e ∧ x e ≤ τ * N.k e) ∧
  (∀ i, ∑ e with N.head e = Sum.inl i, x e ≤ d i) ∧
  (∀ j, ∑ e with N.tail e = Sum.inl j, x e ≤ s j) ∧
  (∀ u : I, ∑ e with N.tail e = Sum.inr u, x e = ∑ e with N.head e = Sum.inr u, x e)

/-- The objective (2a): total value `∑_{(u,w)} v_{u,w} x_{u,w}` of an arc flow. -/
def obj (N : Network nd ns I E) (x : E → ℝ) : ℝ := ∑ e, N.v e * x e

/-- The optimal value `Φ_τ(d, s)` of the LP (2), as the supremum of the objective over the
feasible set. For `τ ≥ 0`, `d ≥ 0`, `s ≥ 0` the feasible set contains `0` and lies in the box
`[0, τ k]`, so the supremum is a maximum; on an infeasible argument Lean's `sSup ∅ = 0`. -/
noncomputable def Phi (N : Network nd ns I E) (τ : ℝ) (d : Fin nd → ℝ) (s : Fin ns → ℝ) : ℝ :=
  sSup (obj N '' {x | Feasible N τ d s x})

/-- `x` is an optimal solution of the LP (2). -/
def IsOptimal (N : Network nd ns I E) (τ : ℝ) (d : Fin nd → ℝ) (s : Fin ns → ℝ) (x : E → ℝ) :
    Prop :=
  Feasible N τ d s x ∧ ∀ y, Feasible N τ d s y → obj N y ≤ obj N x

/-- Dual variables of (5): demand prices `a`, supply prices `b`, node potentials `m` on the
intermediate nodes and capacity prices `ξ` on the arcs. -/
structure DualVar (nd ns : ℕ) (I E : Type) where
  /-- shadow prices `a_i` of the demand constraints (2b) -/
  a : Fin nd → ℝ
  /-- shadow prices `b_j` of the supply constraints (2c) -/
  b : Fin ns → ℝ
  /-- potentials `m_u` of the balance constraints (2d) -/
  m : I → ℝ
  /-- shadow prices `ξ_{u,w}` of the capacity constraints (2e) -/
  ξ : E → ℝ

/-- The dual potential at the tail of an arc: `b_j` at a supply node `u^s_j`, `m_u` at an
intermediate node `u`. -/
def tailPot {N : Network nd ns I E} (q : DualVar nd ns I E) (e : E) : ℝ :=
  match N.tail e with
  | Sum.inl j => q.b j
  | Sum.inr u => q.m u

/-- The dual potential at the head of an arc: `a_i` at a demand node `u^d_i`, `-m_w` at an
intermediate node `w`. -/
def headPot {N : Network nd ns I E} (q : DualVar nd ns I E) (e : E) : ℝ :=
  match N.head e with
  | Sum.inl i => q.a i
  | Sum.inr w => -q.m w

/-- Dual feasibility for (5): one constraint per arc, `tailPot + headPot + ξ ≥ v`, which is
(5b) on supply→demand arcs, (5c) on supply→intermediate arcs, (5d) on intermediate→demand arcs
and (5e) on intermediate→intermediate arcs; and (5f)–(5h) `a ≥ 0`, `b ≥ 0`, `ξ ≥ 0`. -/
def DualFeasible (N : Network nd ns I E) (q : DualVar nd ns I E) : Prop :=
  (∀ e, N.v e ≤ tailPot (N := N) q e + headPot (N := N) q e + q.ξ e) ∧
  (∀ i, 0 ≤ q.a i) ∧ (∀ j, 0 ≤ q.b j) ∧ (∀ e, 0 ≤ q.ξ e)

/-- The dual objective (5a): `∑ a_i d_i + ∑ b_j s_j + ∑ ξ_{u,w} k_{u,w} τ`. -/
def dualObj (N : Network nd ns I E) (τ : ℝ) (d : Fin nd → ℝ) (s : Fin ns → ℝ)
    (q : DualVar nd ns I E) : ℝ :=
  ∑ i, q.a i * d i + ∑ j, q.b j * s j + ∑ e, q.ξ e * N.k e * τ

/-- `q` is an optimal solution of the dual (5): dual feasible and minimizing (5a) among dual
feasible points. -/
def IsOptimalDual (N : Network nd ns I E) (τ : ℝ) (d : Fin nd → ℝ) (s : Fin ns → ℝ)
    (q : DualVar nd ns I E) : Prop :=
  DualFeasible N q ∧ ∀ q', DualFeasible N q' → dualObj N τ d s q ≤ dualObj N τ d s q'

end MarketInterference.FluidBias



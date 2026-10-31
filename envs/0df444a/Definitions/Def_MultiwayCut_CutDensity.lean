-- Prove2me | Definitions.Def_MultiwayCut_CutDensity
-- name    : MultiwayCut_CutDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:06.277596+00:00
-- url     : https://prove2.me/theorems/bf3a0b8d-e594-4d7e-880c-49bebbf046db
-- title:
--   $(i,j)$-edges and the cut density of a randomized labeling
-- statement:
--   1. **$(i,j)$-edge** (Observation 2.1 and Figure 1, pp.4–5). Fix an order $\pi$ of the coordinates. For $1\le i<j\le k$ and $\varepsilon\ge0$, the pair $(\mathbf u,\mathbf v)$ is an $(i,j)$-edge if, writing $u_\ell$ for the $\ell$-th coordinate in the order $\pi$, (1) $u_1\ge\dots\ge u_k$, (2) $u_{i-1}\ge u_i+\varepsilon$ and $u_j-\varepsilon\ge u_{j+1}$, $\mathbf u,\mathbf v\in\Delta_k$, and
--   $$\mathbf v=(u_1,\dots,u_{i-1},u_i+\varepsilon,u_{i+1},\dots,u_{j-1},u_j-\varepsilon,u_{j+1},\dots,u_k).$$
--   2. **Cut density** (Definition 2.1, p.4). For a randomized labeling with separation probability $s(\mathbf u,\mathbf v)=\Pr[g(\mathbf u)\ne g(\mathbf v)]$, the cut density of edges of type $(i,j)$ at $\mathbf u$ is at most $c$ if
--   $$\limsup_{\varepsilon\to0}\frac{s(\mathbf u,\mathbf v_\varepsilon)}{\varepsilon}\le c$$
--   over the $(i,j)$-edges $(\mathbf u,\mathbf v_\varepsilon)$.
--
--   The paper bounds $\alpha_{i,j}$ (CKR) and $\beta_{i,j}$ (exponential clocks) in this sense.
--
--   **Formalization Note** The order is a permutation $\pi$: the paper's $u_\ell$ is `u (π (ℓ-1))`; condition (2) is imposed only when $u_{i-1}$, resp. $u_{j+1}$, exists. "$\limsup\le c$" is written as: for every $\eta>0$, eventually as $\varepsilon\to0^+$, the ratio is at most $c+\eta$, for those $\varepsilon$ at which $(\mathbf u,\mathbf v_\varepsilon)$ is an $(i,j)$-edge (no `Filter.limsup` in $\mathbb R$, which takes a junk value on unbounded functions).
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, Observation 2.1 and Definition 2.1, p.4; Figure 1, p.5

import Mathlib

open Filter Topology

namespace MultiwayCut

variable {k : ℕ}

/-- The point `u + ε (e_a − e_b)`: `u` with `ε` added to coordinate `a` and subtracted from
coordinate `b` (Figure 1, p.5, of Buchbinder, Schwartz & Weizman, *Simplex Transformations and
the Multiway Cut Problem*, manuscript of Nov. 1, 2016). -/
def ijShift (u : Fin k → ℝ) (a b : Fin k) (ε : ℝ) : Fin k → ℝ :=
  u + ε • (Pi.single a 1 - Pi.single b 1)

/-- **`(i, j)`-edge**, manuscript of Nov. 1, 2016, Observation 2.1 and Figure 1, pp.4–5: for
`1 ≤ i < j ≤ k` and `ε ≥ 0`, (1) `u₁ ≥ … ≥ u_k`, (2) `u_{i−1} ≥ uᵢ + ε` and
`u_j − ε ≥ u_{j+1}`, and `v` is `u` with `uᵢ` raised by `ε` and `u_j` lowered by `ε`; both
`u, v ∈ Δ_k`. The order of the coordinates is the one in which `u` (and `v`) are non-increasing
("there exists an order of the coordinates such that both u and v are non-increasing with
respect to this order", p.4).

**Formalization Note.** The order is a permutation `π`: the paper's `u_ℓ` is `u (π (ℓ − 1))`
(0-based positions). Condition (2) is required only when `u_{i−1}`, resp. `u_{j+1}`, exists
(`i` not the first, `j` not the last position). -/
def IsIJEdge (π : Equiv.Perm (Fin k)) (i j : Fin k) (ε : ℝ) (u v : Fin k → ℝ) : Prop :=
  u ∈ stdSimplex ℝ (Fin k) ∧ v ∈ stdSimplex ℝ (Fin k) ∧ i < j ∧ 0 ≤ ε ∧
    Antitone (u ∘ π) ∧
    (∀ i' : Fin k, i'.val + 1 = i.val → u (π i) + ε ≤ u (π i')) ∧
    (∀ j' : Fin k, j'.val = j.val + 1 → u (π j') ≤ u (π j) - ε) ∧
    v = ijShift u (π i) (π j) ε

/-- **Cut density at most `c`** for edges of type `(i, j)` at the point `u`, manuscript of
Nov. 1, 2016, Definition 2.1, p.4: for every edge `(u, v)` of type `(i, j)` (with the order `π`),
`lim sup_{ε→0} Pr[g(u) ≠ g(v)] / ε ≤ c`, where `s u v` is the separation probability
`Pr[g(u) ≠ g(v)]` of the randomized labeling and `v = u + ε(e_{π i} − e_{π j})`.

**Formalization Note.** `lim sup_{ε→0⁺} φ(ε) ≤ c` is written as: for every `η > 0`,
eventually as `ε → 0⁺`, `φ(ε) ≤ c + η` (no `Filter.limsup` in `ℝ`, whose value on an unbounded
function is a junk value). The limit is one-sided because an edge has `ε ≥ 0`. The bound is
required only for those `ε` for which `(u, v)` is an `(i, j)`-edge (`IsIJEdge`), which is the
paper's "for every edge (u, v) of type (i, j)". -/
def IJDensityLE (s : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (π : Equiv.Perm (Fin k)) (i j : Fin k)
    (u : Fin k → ℝ) (c : ℝ) : Prop :=
  ∀ η > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    IsIJEdge π i j ε u (ijShift u (π i) (π j) ε) →
      s u (ijShift u (π i) (π j) ε) / ε ≤ c + η

end MultiwayCut



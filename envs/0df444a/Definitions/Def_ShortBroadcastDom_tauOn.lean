-- Prove2me | Definitions.Def_ShortBroadcastDom_tauOn
-- name    : ShortBroadcastDom_tauOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:16.265363+00:00
-- url     : https://prove2.me/theorems/ee2c8956-2c0b-426c-b2e8-f4eae9d2fa1b
-- title:
--   The covering LP value $\tau_{R,c}(G)$ and the fractional domination number $\gamma_f(G)$
-- statement:
--   Let $G$ be a finite graph, $R\subseteq V(G)$ a set of **demands** and $c=(c_v)$ vertex **costs**. The fractional covering program (eq. (1) of the paper) has optimum
--
--   $$
--   \tau_{R,c}(G)=\min\Bigl\{\sum_{v\in V(G)}c_vx_v:\ x_v\ge 0,\ \sum_{v\in N_G[r]}x_v\ge 1\ (r\in R)\Bigr\}.
--   $$
--
--   Every vertex may be used as a candidate; only the demands must be covered. The **fractional domination number** is the special case of unit costs and all vertices as demands:
--
--   $$
--   \gamma_f(G)=\tau_{V(G),\mathbf 1}(G).
--   $$
--
--   More generally, for a candidate set $C$, the value $\tau^C_{R,c}(G)$ is the same minimum over vectors $x$ that vanish outside $C$; with $C$ the candidate set of the rounding rule this is the value $C^*$ of §7 ("the minimum cost of a fractional cover of $R_0$ using only candidates in $C$").
--
--   **Formalization Note** The optimum is the infimum (`sInf` in $\mathbb R$) of the feasible objective values. For costs $c\ge 0$ the feasible set is bounded below by $0$, and it is nonempty whenever every demand has a candidate in its closed neighbourhood, so the infimum is the LP minimum. On an infeasible program Lean's convention gives $0$; no statement of the mission uses that case. Costs are real numbers (the paper uses integer costs in (1) and "the same notation … with positive real costs" on p.15).
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), eq. (1) §4, p.14 (PDF p.17); p.15 (PDF p.18); §7.1, p.45 (PDF p.48)

import Mathlib
import Definitions.Def_ShortBroadcastDom_closedNbhd

namespace ShortBroadcastDom

/-- **The covering LP value `τ_{R,c}` with candidates restricted to `C`.** For a candidate set
`C`, a demand set `R` and vertex costs `c`, `tauOn G C R c` is
`inf { ∑_v c_v x_v : x ≥ 0, x_v = 0 for v ∉ C, ∑_{v ∈ N_G[r]} x_v ≥ 1 (r ∈ R) }`.

Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), eq. (1), §4, p.14 (PDF 17), and §7.1, p.45 (PDF 48): "let C∗ be the minimum cost of a
fractional cover of R0 using only candidates in C".

**Formalization Note** The optimum is `sInf` over `ℝ` of the feasible objective values. For costs
`c ≥ 0` the set is bounded below by `0`, and whenever every demand has a candidate of `C` in its
closed neighbourhood it is nonempty (put `x = 1` on `C`), so `sInf` is the LP minimum. If some
demand has no candidate in `C` the program is infeasible and Lean's `sInf ∅ = 0`; no statement of
the mission uses `tauOn` in that case (there `R ⊆ C`, so each demand covers itself). -/
noncomputable def tauOn {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (C R : Finset V) (c : V → ℝ) : ℝ :=
  sInf {s : ℝ | ∃ x : V → ℝ, (∀ v, 0 ≤ x v) ∧ (∀ v, v ∉ C → x v = 0) ∧
    (∀ r ∈ R, 1 ≤ ∑ v ∈ closedNbhd G r, x v) ∧ s = ∑ v, c v * x v}

/-- **The covering LP value `τ_{R,c}(G)`** of eq. (1), §4, p.14 (PDF 17):
`τ_{R,c}(G) = min { ∑_{v ∈ V(G)} c_v x_v : x_v ≥ 0, ∑_{v ∈ N_G[r]} x_v ≥ 1 (r ∈ R) }`;
every vertex of `G` is a candidate and only the demands in `R` must be covered.

**Formalization Note** `tau G R c = tauOn G univ R c`. Costs are real; the paper's (1) uses integer
costs `1 ≤ c_v ≤ B₀`, and p.15 (PDF 18) uses "the same notation … with positive real costs". For
`c ≥ 0` the feasible set is nonempty (`x ≡ 1`) and bounded below by `0`, so `sInf` is the minimum. -/
noncomputable def tau {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (R : Finset V) (c : V → ℝ) : ℝ :=
  tauOn G Finset.univ R c

/-- **The fractional domination number `γ_f(G)`**, §4, p.14 (PDF 17): "the minimum of ∑_v x_v
subject to ∑_{v ∈ N[r]} x_v ≥ 1 for every vertex r", i.e. `τ_{V(G),1}(G)`.

**Formalization Note** The feasible set contains `x ≡ 1` and is bounded below by `0`, so this
`sInf` is the minimum; for the graph with no vertices it is `0`. -/
noncomputable def fracDom {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℝ :=
  tau G Finset.univ (fun _ => 1)

end ShortBroadcastDom



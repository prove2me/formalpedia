-- Prove2me | Definitions.Def_MetricTSPSublinear_cutLP
-- name    : MetricTSPSublinear_cutLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:24:14.81146+00:00
-- url     : https://prove2.me/theorems/6b14e770-0847-41e4-b908-b3ebce325fdc
-- title:
--   The cut LP value $K(S)$ of a metric
-- statement:
--   Let $d$ be a metric on $V$ and $S\subseteq V$. For $\emptyset\ne A\subsetneq S$ write $\delta_S(A)$ for the set of unordered pairs $\{u,v\}$ with $u\in A$ and $v\in S\setminus A$. The **cut relaxation of the minimum spanning tree** on $S$ is the linear program
--   $$K(S)=\min\Big\{\sum_{e}w_e x_e\ :\ x(\delta_S(A))\ge 1\ \ (\emptyset\ne A\subsetneq S),\ x\ge 0\Big\},$$
--   where $e$ ranges over the pairs $\{u,v\}\subseteq S$ with $u\ne v$ and $w_{\{u,v\}}=d(u,v)$. The paper's $K$ is $K(V)$.
--
--   $K$ is the central quantity of the paper: it lies between $M/2$ and $M$ ($M$ the MST weight), and the TSP value lies between $\max(M,2K)$ and $M+K$.
--
--   **Formalization Note.** The value is the infimum of the objective over the feasible points; the feasible set is nonempty ($x\equiv1$) and the objective is nonnegative for a metric, so this is the LP's optimum. For $|S|\le1$ there is no cut and the value is $0$. The weight of a pair is the published `DoublingMST.edgeCost`, $\min(d(u,v),d(v,u))$, which is $d(u,v)$ for a metric.
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §2.1, p.2 (PDF p.4), display (P); §3, p.9 (PDF p.11); §4.2, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_DoublingMST_edgeCost

open scoped Classical

namespace MetricTSPSublinear

/-!
# The cut LP `K(S)` of a metric

Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §2.1, p.2 (PDF p.4), display (P):
`K = min { ∑_e w_e x_e | x(δ(A)) ≥ 1 (∅ ≠ A ⊊ V), x ≥ 0 }`; §3, p.9 (PDF p.11): "K to denote the optimal value of
the Cut LP"; §4.2, p.14 (PDF p.16): "K(S) is the optimal value of the Cut LP on the metric induced by a vertex set S".
-/

/-- The edges of the complete graph on `S`: the unordered pairs `{u, v}` with `u ≠ v`, `u, v ∈ S`. -/
def pairsIn {n : ℕ} (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  S.sym2.filter (fun e => ¬ e.IsDiag)

/-- The cut `δ_S(A)`: the pairs `{u, v}` with `u ∈ A` and `v ∈ S \ A`. Each crossing pair occurs once. -/
def cutEdges {n : ℕ} (S A : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  (A ×ˢ (S \ A)).image (fun p => s(p.1, p.2))

/-- A feasible point of (P) on `S`: `x ≥ 0` and `x(δ_S(A)) ≥ 1` for every `∅ ≠ A ⊊ S`. -/
def IsCutFeasible {n : ℕ} (S : Finset (Fin n)) (x : Sym2 (Fin n) → ℝ) : Prop :=
  (∀ e, 0 ≤ x e) ∧ ∀ A ⊆ S, A.Nonempty → A ≠ S → 1 ≤ ∑ e ∈ cutEdges S A, x e

/-- **The cut LP value `K(S)`** of the metric `d` induced on `S`: the infimum of `∑_{e} w_e x_e` over the pairs `e`
inside `S`, where `w_{uv} = d(u, v)`, over the feasible points of (P) on `S`. The paper's `K` is
`cutLP d Finset.univ`.

**Formalization Note.** The variables are indexed by all unordered pairs; only the pairs inside `S` enter the
objective and the cuts, so the others are irrelevant. The feasible set is nonempty (`x ≡ 1`), and for a metric the
objective is `≥ 0`, so the infimum is the LP's optimal value (an LP with finite infimum attains it). For `|S| ≤ 1`
there is no cut and no pair, and the value is `0`. The weight of a pair is the published `DoublingMST.edgeCost`,
`min (d u v) (d v u)`, which is `d u v` for a metric. For a non-metric `d` the infimum can be over an unbounded-below
set and is then the junk value `0`; every statement in this mission assumes a metric. -/
noncomputable def cutLP {n : ℕ} (d : Fin n → Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  sInf {t : ℝ | ∃ x : Sym2 (Fin n) → ℝ, IsCutFeasible S x ∧
    t = ∑ e ∈ pairsIn S, DoublingMST.edgeCost d e * x e}

end MetricTSPSublinear



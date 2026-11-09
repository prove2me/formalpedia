-- Prove2me | Definitions.Def_MetricTSPSublinear_IsDualFeasible
-- name    : MetricTSPSublinear_IsDualFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:23:43.738534+00:00
-- url     : https://prove2.me/theorems/9b8aa69d-1d24-4821-bfbe-f7bd0bef9b2f
-- title:
--   Feasible solutions of the dual cut LP (5)
-- statement:
--   For a metric $d$ on $V$ and $S\subseteq V$, a **feasible dual solution** on $S$ is a family $(y_A)$ of reals indexed by the cuts $\emptyset\ne A\subsetneq S$ with $y\ge0$ and
--   $$\sum_{A:\ \{u,v\}\in\delta(A)} y_A\ \le\ d(u,v)\qquad\text{for all } u\ne v \text{ in } S.$$
--   Its value is $\sum_A y_A$. By LP duality the largest value is $K(S)$ (display (5) of the paper for $S=V$).
--
--   The paper represents dual solutions by Steiner trees (Claim 4.1, Lemma 4.2).
--
--   **Formalization Note.** $y$ is a function on all subsets of $V$ that vanishes off the cuts $\emptyset\ne A\subsetneq S$.
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §4.1, p.12 (PDF p.14), display (5)

import Mathlib

open scoped Classical

namespace MetricTSPSublinear

/-- **A feasible solution of the dual cut LP (5) on `S`.**
Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §4.1, p.12 (PDF p.14), display (5):
`K = max { ∑_{∅≠A⊊V} y_A | ∑_{A: e∈δ(A)} y_A ≤ w_e (∀e), y ≥ 0 }`, "Here e = (u, v) ranges over all pairs u ≠ v ∈ V,
and w_e is given by the metric distance d(u, v)."

`IsDualFeasible d S y` for `y : Finset (Fin n) → ℝ` says: `y ≥ 0`; `y A = 0` unless `A ⊆ S`, `A ≠ ∅` and `A ≠ S`
(the dual variables are indexed by the cuts `∅ ≠ A ⊊ S`); and for all `u ≠ v` in `S`, the sum of `y A` over the sets
`A` that separate `u` from `v` is at most `d u v`. Its value is `∑ A, y A`.

**Formalization Note.** `S = Finset.univ` gives the paper's (5) on `V`; general `S` is the dual on the metric induced
by `S`, used for `K(S)` (p.14, p.16). -/
def IsDualFeasible {n : ℕ} (d : Fin n → Fin n → ℝ) (S : Finset (Fin n)) (y : Finset (Fin n) → ℝ) : Prop :=
  (∀ A, 0 ≤ y A) ∧ (∀ A, ¬ (A ⊆ S ∧ A.Nonempty ∧ A ≠ S) → y A = 0) ∧
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin n) => ¬ ((u ∈ A) ↔ (v ∈ A))), y A ≤ d u v

end MetricTSPSublinear



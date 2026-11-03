-- Prove2me | Definitions.Def_RegimeDRCVaR_empiricalMeasure
-- name    : RegimeDRCVaR_empiricalMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:45.339644+00:00
-- url     : https://prove2.me/theorems/bfc34091-2fd7-4af0-acbe-e89ced758006
-- title:
--   Empirical distribution $\hat{\mathbb P}_k$ of regime $k$
-- statement:
--   The **empirical distribution** of regime $k$ is
--   $$
--   \hat{\mathbb P}_k=\frac1{N_k}\sum_{n\in[N_k]}\delta_{r_{nk}},
--   $$
--   the uniform law on the $N_k$ return samples of that regime. It is the center of the regime-$k$ Wasserstein ball in Lemma EC.1.
--
--   **Formalization Note** A measure on $\mathbb R^I$ with its Borel $\sigma$-algebra; it is a probability measure when $N_k\ge1$.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, p.11 below display (9); Lemma EC.1, p.ec1

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace RegimeDRCVaR

/-- **The empirical distribution of regime `k`** `P̂_k = (1/N_k) ∑_{n∈[N_k]} δ_{r_{nk}}`
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, p.11 below (9), and Lemma EC.1, p.ec1).

**Formalization Note** A measure on `ℝ^I = Fin I → ℝ` (Borel σ-algebra); it is a probability
measure when `N_k ≥ 1`. -/
noncomputable def empiricalMeasure {I K : ℕ} {N : Fin K → ℕ}
    (r : (k : Fin K) → Fin (N k) → Fin I → ℝ) (k : Fin K) : Measure (Fin I → ℝ) :=
  ∑ n : Fin (N k), ((N k : ℝ≥0∞)⁻¹) • Measure.dirac (r k n)

end RegimeDRCVaR



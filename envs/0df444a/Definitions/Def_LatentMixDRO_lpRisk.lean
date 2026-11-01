-- Prove2me | Definitions.Def_LatentMixDRO_lpRisk
-- name    : LatentMixDRO_lpRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:40.296767+00:00
-- url     : https://prove2.me/theorems/7000df09-c9c5-47a4-882b-1781c8e8d2aa
-- title:
--   $L^p$ risk $(\mathbb E_{X\sim P_X}[(f(X)-\eta)_+^p])^{1/p}$
-- statement:
--   For $P$ a law on $\mathbb R^d\times\mathbb R$ with covariate marginal $P_X$, $p>1$, $f:\mathbb R^d\to\mathbb R$ and $\eta\in\mathbb R$, the **$L^p$ risk** is
--
--   $$
--   \Big(\mathbb E_{X\sim P_X}\big[(f(X)-\eta)_+^{\,p}\big]\Big)^{1/p}.
--   $$
--
--   With $f$ the conditional risk, this is the $L^p$ upper bound on the CVaR dual objective that the marginal DRO estimator approximates.
--
--   **Formalization Note** A Bochner integral: under A1 and A3 the integrand is bounded and almost everywhere measurable.
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, display (9), p.9, and the bound (5), p.4

import Mathlib

open MeasureTheory

namespace LatentMixDRO

/-- The `L^p` risk `(E_{X∼P_X}[(f(X) - η)₊^p])^{1/p}`, with `P_X` the first marginal of `P`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, display (9), p.9, and the bound (5), p.4.

**Formalization Note.** A Bochner integral: under the paper's assumptions the integrand is bounded
and almost everywhere measurable, so the integral is the true one. -/
noncomputable def lpRisk {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) (p : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (η : ℝ) : ℝ :=
  (∫ x, (max (f x - η) 0) ^ p ∂(P.map Prod.fst)) ^ (1 / p)

end LatentMixDRO



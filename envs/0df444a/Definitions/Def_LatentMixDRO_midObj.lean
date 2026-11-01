-- Prove2me | Definitions.Def_LatentMixDRO_midObj
-- name    : LatentMixDRO_midObj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:21.304653+00:00
-- url     : https://prove2.me/theorems/f5f9b91a-945f-4b84-b0ae-0d2bf9294a15
-- title:
--   $L^p$ bound at a fixed conditional risk
-- statement:
--   For a conditional risk $f$,
--
--   $$
--   \inf_{\eta\in[0,M]}\Big\{\frac1{\alpha_0}\Big(\mathbb E\big[(f(X)-\eta)_+^{\,p}\big]\Big)^{1/p}+\eta\Big\}.
--   $$
--
--   At $f=\mathbb E[\ell(\hat\theta;(X,Y))\mid X]$ it is the middle term of (18).
--
--   **Formalization Note** The real infimum over $[0,M]$ is the true one: the interval is nonempty for $M\ge0$ and the values are nonnegative for $\alpha_0>0$.
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, Theorem 1, display (18), p.11

import Mathlib
import Definitions.Def_LatentMixDRO_lpRisk

open MeasureTheory

namespace LatentMixDRO

/-- The `L^p` bound at a fixed conditional risk `f`, the middle term of (18):
`inf_{η ∈ [0,M]} {(1/α₀) (E[(f(X) - η)₊^p])^{1/p} + η}`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, Theorem 1, display (18), p.11.

**Formalization Note.** A real `⨅` over `[0, M]`: nonempty for `M ≥ 0`, and the values are at least
`0` for `α₀ > 0`, so it is the true infimum. -/
noncomputable def midObj {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) (p α₀ M : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  ⨅ η : Set.Icc (0 : ℝ) M, (1 / α₀) * lpRisk P p f η + η

end LatentMixDRO



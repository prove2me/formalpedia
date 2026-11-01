-- Prove2me | Definitions.Def_LatentMixDRO_lowObj
-- name    : LatentMixDRO_lowObj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:33.774411+00:00
-- url     : https://prove2.me/theorems/cc76c46c-ef03-4120-948d-49fb9e571ef0
-- title:
--   Optimal value of the $L^p$ bound
-- statement:
--   With $z_\theta$ the conditional risk of $\theta$,
--
--   $$
--   \inf_{\theta\in\Theta,\ \eta\in[0,M]}\Big\{\frac1{\alpha_0}\Big(\mathbb E\big[(z_\theta(X)-\eta)_+^{\,p}\big]\Big)^{1/p}+\eta\Big\}.
--   $$
--
--   It is the benchmark on the right side of (18).
--
--   **Formalization Note** The values are nonnegative for $\alpha_0>0$, and Theorem 1 uses this infimum only with a minimizer $\hat\theta\in\Theta$ in hand, so the index set is nonempty.
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, Theorem 1, display (18), p.11

import Mathlib
import Definitions.Def_LatentMixDRO_lpRisk

open MeasureTheory

namespace LatentMixDRO

/-- The optimal value of the `L^p` bound, the last infimum of (18):
`inf_{θ ∈ Θ, η ∈ [0,M]} {(1/α₀) (E[(z_θ(X) - η)₊^p])^{1/p} + η}`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, Theorem 1, display (18), p.11.

**Formalization Note.** A real `⨅`: the values are at least `0` for `α₀ > 0`, and the index type is
nonempty as soon as `Θ` is and `M ≥ 0`. Theorem 1 uses it only with a minimizer `θ̂ : Θ` in hand. -/
noncomputable def lowObj {d : ℕ} {Θ : Type*} (P : Measure (EuclideanSpace ℝ (Fin d) × ℝ))
    (p α₀ M : ℝ) (z : Θ → EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  ⨅ a : Θ × Set.Icc (0 : ℝ) M, (1 / α₀) * lpRisk P p (z a.1) a.2 + a.2

end LatentMixDRO



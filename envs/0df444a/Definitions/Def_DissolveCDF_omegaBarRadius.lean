-- Prove2me | Definitions.Def_DissolveCDF_omegaBarRadius
-- name    : DissolveCDF_omegaBarRadius
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:35:09.21718+00:00
-- url     : https://prove2.me/theorems/22275805-d1f4-4783-8333-a8b1f8d92b3f
-- title:
--   §2.3 — the radius of $\bar\Omega_x$
-- statement:
--   For $x\in\mathcal M$, the paper sets
--
--   $$
--   \bar\Omega_x:=\Big\{y\in\mathbb R^n:\ \|y-x\|\le\frac{\sigma_{x,c}\,\varepsilon_x}{4M_{x,c}(M_{x,A}+1)+\sigma_{x,c}}\Big\}.
--   $$
--
--   This definition is the radius on the right; $\bar\Omega_x\subset\Omega_x$. Lemma 3.4, Proposition 3.13 and Theorem 3.18 are stated on $\bar\Omega_x$.
--
--   **Formalization Note** In Lean $\bar\Omega_x$ is `Metric.closedBall x (omegaBarRadius c A x)`. For $x\in\mathcal M$ (and $p\ge1$) the denominator is positive, so Lean's division is the paper's.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, §2.3, p.7

import Mathlib
import Definitions.Def_DissolveCDF_sigmaXC
import Definitions.Def_DissolveCDF_MXc
import Definitions.Def_DissolveCDF_MXA
import Definitions.Def_DissolveCDF_epsX

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, §2.3 (p.7): the radius of
`Ω̄_x := {y ∈ ℝⁿ : ‖y − x‖ ≤ σ_{x,c} ε_x / (4 M_{x,c}(M_{x,A} + 1) + σ_{x,c})}`, so that
`Ω̄_x = Metric.closedBall x (omegaBarRadius c A x)`.

**Formalization Note** For `x ∈ M` the denominator is positive (`σ_{x,c} > 0`, `M_{x,c} ≥ 0`,
`M_{x,A} ≥ 0`), so Lean's division is the paper's. -/
noncomputable def omegaBarRadius {n p : ℕ} (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sigmaXC c x * epsX c A x / (4 * MXc c x * (MXA c A x + 1) + sigmaXC c x)

end DissolveCDF



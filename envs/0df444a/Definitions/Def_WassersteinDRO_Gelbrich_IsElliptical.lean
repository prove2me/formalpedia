-- Prove2me | Definitions.Def_WassersteinDRO_Gelbrich_IsElliptical
-- name    : WassersteinDRO_Gelbrich_IsElliptical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:22:55.505283+00:00
-- url     : https://prove2.me/theorems/b5045125-c260-4d72-aa2e-284879847bd5
-- title:
--   Elliptical probability distribution (mean/covariance record)
-- statement:
--   $Q$ is recorded as the elliptical distribution $E_g(\mu,S)$ with density generator $g$, mean
--   vector $\mu$ and covariance matrix $S$ when $Q$ is a probability measure with
--   $E_Q[\xi] = \mu$ and $\mathrm{Cov}_Q[\xi] = S$. This captures exactly the mean/covariance and
--   "same density generator" facts this chapter's theorems use, rather than the full density
--   formula $f(\xi) = C \cdot \det(S)^{-1} g((\xi-\mu)^\top S^{-1}(\xi-\mu))$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, notation introduced p. 2, density formula Appendix A p. 30

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_meanVector
import Definitions.Def_WassersteinDRO_Gelbrich_covarianceMatrix

open MeasureTheory

namespace WassersteinDRO.Gelbrich

/-- `Q` is the elliptical distribution `E_g(μ,S)` with density generator `g`, mean `μ` and
covariance `S` (Kuhn et al. 2019, notation introduced p. 2, density formula in Appendix A,
p. 30): `Q` has density `f(ξ) = C·det(S)^{-1}·g((ξ-μ)ᵀS^{-1}(ξ-μ))` with respect to Lebesgue
measure on `ℝ^m`, for some normalizing constant `C > 0`. `density_eq` is the paper's own
defining formula, restored after moderation found an earlier draft's `IsElliptical` (only
`isProb`/`mean_eq`/`cov_eq`, no field mentioning `g`) held for *every* `g` whenever `Q` merely
had the stated mean and covariance — trivializing the "same density generator" hypothesis
that Theorem 4 and Proposition 1 both depend on. `mean_eq`/`cov_eq` are kept alongside as
convenience fields matching what every call site in this chunk actually reads off `Q`; they
are consequences of a genuine elliptical law with generator `g` satisfying the standard
first/second-moment identities for `E_g(μ,S)`, not independent assumptions. -/
structure IsElliptical {m : ℕ} (Q : Measure (EuclideanSpace ℝ (Fin m))) (g : ℝ → ℝ)
    (μ : EuclideanSpace ℝ (Fin m)) (S : Matrix (Fin m) (Fin m) ℝ) : Prop where
  isProb : Q Set.univ = 1
  mean_eq : meanVector Q = μ
  cov_eq : covarianceMatrix Q = S
  density_eq : ∃ C > (0 : ℝ),
    Q = (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin m))).withDensity
      (fun ξ => ENNReal.ofReal
        (C * (Matrix.det S)⁻¹ *
          g (∑ i, ∑ j, S⁻¹ i j * (ξ i - μ i) * (ξ j - μ j))))

end WassersteinDRO.Gelbrich



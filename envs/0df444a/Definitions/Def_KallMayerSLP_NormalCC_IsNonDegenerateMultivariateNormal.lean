-- Prove2me | Definitions.Def_KallMayerSLP_NormalCC_IsNonDegenerateMultivariateNormal
-- name    : KallMayerSLP_NormalCC_IsNonDegenerateMultivariateNormal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:05.633109+00:00
-- url     : https://prove2.me/theorems/c3e98539-e017-4bf6-9d51-239ccfe713fb
-- title:
--   Non-degenerate multivariate normal random vector (covariance $BB^{\mathsf T}$ positive definite)
-- statement:
--   An $r$-dimensional random vector $\zeta=B\tilde\zeta+\mu$, multivariate normal in the sense of Definition 2.1, has covariance matrix $\Sigma=BB^{\mathsf T}$. Its distribution is **non-degenerate** if $\Sigma$ is positive definite; equivalently, $B$ has full row rank.
--
--   Here: $\zeta$ is non-degenerate multivariate normal if it admits a representation $\zeta=B\tilde\zeta+\mu$ ($\tilde\zeta$ a vector of independent standard normal variables, equality almost surely) with $BB^{\mathsf T}$ positive definite.
--
--   Non-degeneracy is the hypothesis of Theorem 2.6, of (2.36) and of Proposition 2.1. For $\zeta=(\eta^{\mathsf T},\xi)^{\mathsf T}$ it means that $D^{\mathsf T}x-d\neq0$ for every $x$ (p.109).
--
--   **Formalization Note** Since $BB^{\mathsf T}$ is the covariance matrix of $\zeta$, the condition does not depend on which representation is chosen.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, p.104 (PDF p.114), definition of non-degenerate; p.109 (PDF p.119)

import Mathlib
import Definitions.Def_HighDimProb_RandomVectors_IsStandardGaussianVector

open MeasureTheory ProbabilityTheory

namespace KallMayerSLP.NormalCC

/-- **Non-degenerate multivariate normal distribution** (Kall & Mayer 2005, Chapter 2, p.104,
PDF p.114): for `ζ = B ζ̃ + μ` as in Definition 2.1, "`Σ = B Bᵀ`, where `Σ` denotes the covariance
matrix of `ζ` … The multivariate normal distribution is called *non-degenerate*, if `Σ` is positive
definite. This is the case if and only if `B` has full row rank."

**Formalization Note.** Encoded as: `ζ` has a representation `ζ = B ζ̃ + μ` (almost surely) with
`ζ̃` a standard Gaussian vector (as in `IsMultivariateNormal`) and the covariance matrix
`Σ = B Bᵀ` positive definite. Since `B Bᵀ` is the covariance matrix of `ζ`, it does not depend on
the representation chosen. -/
def IsNonDegenerateMultivariateNormal {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {r : ℕ}
    (ζ : Ω → Fin r → ℝ) : Prop :=
  ∃ (s : ℕ) (B : Matrix (Fin r) (Fin s) ℝ) (μ : Fin r → ℝ) (ζt : Fin s → Ω → ℝ),
    HighDimProb.RandomVectors.IsStandardGaussianVector P ζt ∧
      (∀ᵐ ω ∂P, ζ ω = B.mulVec (fun j => ζt j ω) + μ) ∧
      (B * B.transpose).PosDef

end KallMayerSLP.NormalCC



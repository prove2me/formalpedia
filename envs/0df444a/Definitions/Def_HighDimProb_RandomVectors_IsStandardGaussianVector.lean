-- Prove2me | Definitions.Def_HighDimProb_RandomVectors_IsStandardGaussianVector
-- name    : HighDimProb_RandomVectors_IsStandardGaussianVector
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T06:40:06.707002+00:00
-- url     : https://prove2.me/theorems/2ce3e582-d370-4095-87c2-d84b76cc8484
-- title:
--   Standard Gaussian random vector
-- statement:
--   This definition operationally characterizes a **standard Gaussian random vector**
--   $g \sim N(0, I_n)$ in $\mathbb R^n$, the hypothesis of Grothendieck's identity
--   (Lemma 3.6.6).
--
--   Let $(\Omega, \mathcal F, P)$ be a probability space and $g = (g_1, \dots, g_n) : \Omega \to
--   \mathbb R^n$ a random vector, represented coordinatewise as $g : \{1,\dots,n\} \to \Omega \to
--   \mathbb R$. $g$ is a **standard Gaussian random vector** when its coordinates $g_1, \dots,
--   g_n$ are measurable, (jointly) independent, and each has the real standard normal law
--   $N(0,1)$.
--
--   Vershynin's book introduces $N(0, I_n)$ as the multivariate normal distribution with
--   covariance $\Sigma = I_n$; since the coordinates of a jointly Gaussian vector are
--   independent exactly when they are uncorrelated (§3.3.2), and $\Sigma = I_n$ says precisely
--   that the coordinates are uncorrelated with unit variance, a vector of independent $N(0,1)$
--   coordinates is exactly $N(0, I_n)$. This definition takes that equivalent, coordinatewise
--   characterization as primitive.
--
--   **Formalization Note** `gaussianReal 0 1` is Mathlib's real standard normal law. No
--   dimension `n = 0` or `n = 1` corner case is excluded; at `n = 0` the condition is vacuously
--   true of every (necessarily empty) family of coordinate functions.
-- source:
--   Vershynin, High-Dimensional Probability (2018), §3.3.2, p. 51 (PDF p. 59), and Exercise 3.3.5(b)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace HighDimProb.RandomVectors

/-- `g` is a standard Gaussian random vector in `ℝⁿ`, i.e. `g ∼ N(0, Iₙ)`. Vershynin,
*High-Dimensional Probability* (2018), §3.3.2: the coordinates of `N(0, Iₙ)` are independent
(since `Σ = In` means the coordinates are uncorrelated, and for a jointly Gaussian vector
uncorrelated is equivalent to independent), and each coordinate has the standard real
Gaussian law `N(0, 1)`. This is the operational definition used here: `g` is a vector of `n`
independent, real-valued random variables, each distributed `gaussianReal 0 1`. -/
def IsStandardGaussianVector {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (g : Fin n → Ω → ℝ) : Prop :=
  (∀ i, Measurable (g i)) ∧ iIndepFun g P ∧
    ∀ i, Measure.map (g i) P = gaussianReal 0 1

end HighDimProb.RandomVectors



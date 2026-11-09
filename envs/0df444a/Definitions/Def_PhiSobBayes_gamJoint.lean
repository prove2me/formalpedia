-- Prove2me | Definitions.Def_PhiSobBayes_gamJoint
-- name    : PhiSobBayes_gamJoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:05:17.79519+00:00
-- url     : https://prove2.me/theorems/a48eb155-645c-4777-b4c5-fdc4255eb1f8
-- title:
--   Planted model $P_t=\mathcal L(X,Y_t)$ of the Gaussian additive model
-- statement:
--   In the **Gaussian additive model** with prior $\mu$ and signal-to-noise ratio $t$, a signal $X\sim\mu$ is observed as
--   $$Y_t=\sqrt t\,X+G,\qquad G\sim\mathcal N(0,I_n)\ \text{independent of }X.$$
--   Equivalently, given $X=x$ the observation has law $K_{t,x}=\mathcal N(\sqrt t\,x,I_n)$ (the Gaussian channel). The **planted model** is the joint law $P_t=\mathcal L(X,Y_t)$, i.e. $P_t(dx,dy)=\mu(dx)K_{t,x}(dy)$.
--
--   The Bayes risk is an expectation under $P_t$.
--
--   **Formalization Note** $P_t$ is the pushforward of $\mu\otimes\gamma_n$ under $(x,g)\mapsto(x,\sqrt t\,x+g)$, where $\gamma_n=\mathcal N(0,I_n)$ is Mathlib's `stdGaussian` on `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Definition 4, p.14 (PDF 14); p.15 (PDF 15)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- The **planted model** `P_t = L(X, Y_t)` of the Gaussian additive model: `X ∼ μ`,
`Y_t = √t X + G` with `G ∼ N(0, I_n)` independent of `X`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Definition 4, p.14 (PDF 14), and "Observation laws and the planted model", p.15 (PDF 15):
"We call the joint law 𝑃𝑡 := L(𝑋, 𝑌𝑡) of the signal 𝑋 ∼ 𝜇 and the observation the planted model".

**Formalization Note** The law of `(X, √t X + G)` is the pushforward of `μ ⊗ γ_n` by
`(x, g) ↦ (x, √t x + g)`, where `γ_n = N(0, I_n)` is Mathlib's `stdGaussian` on
`EuclideanSpace ℝ (Fin n)`. This is `μ(dx) K_{t,x}(dy)` with `K_{t,x} = N(√t x, I_n)`. -/
noncomputable def gamJoint {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  (μ.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => (p.1, Real.sqrt t • p.1 + p.2))

end PhiSobBayes



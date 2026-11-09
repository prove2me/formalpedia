-- Prove2me | Definitions.Def_PhiSobBayes_gamObs
-- name    : PhiSobBayes_gamObs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:05:19.403071+00:00
-- url     : https://prove2.me/theorems/77252f60-58da-4966-96e9-2c2c23349d1b
-- title:
--   Observation law $\zeta K_t$
-- statement:
--   For a probability measure $\zeta$ on $\mathbb R^n$, the **observation law**
--   $$\zeta K_t=\int K_{t,x}\,\zeta(dx)$$
--   is the law of $Y_t=\sqrt t\,X+G$ when $X\sim\zeta$ and $G\sim\mathcal N(0,I_n)$ is independent of $X$. For the prior $\mu$ it is the law of the observation, $Y_t\sim\mu K_t$.
--
--   It is the averaging law in (46), Lemma 6.2 and Fact A.25.
--
--   **Formalization Note** The pushforward of $\zeta\otimes\gamma_n$ under $(x,g)\mapsto\sqrt t\,x+g$, with $\gamma_n$ Mathlib's `stdGaussian`.
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), p.15 (PDF 15), "Observation laws and the planted model"

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- The **observation law** `ζK_t = ∫ K_{t,x} ζ(dx)`: the law of `Y_t = √t X + G` when `X ∼ ζ` and
`G ∼ N(0, I_n)` is independent of `X`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), "Observation laws and the planted model", p.15 (PDF 15): "For a probability measure 𝜁 on
ℝ𝑛, we denote by 𝜁𝐾𝑡 := ∫ 𝐾_{𝑡,𝑥} 𝜁(d𝑥) the law of the observation 𝑌𝑡 when 𝑋 ∼ 𝜁".

**Formalization Note** The pushforward of `ζ ⊗ γ_n` by `(x, g) ↦ √t x + g`, with `γ_n` Mathlib's
`stdGaussian`. -/
noncomputable def gamObs {n : ℕ} (ζ : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (ζ.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => Real.sqrt t • p.1 + p.2)

end PhiSobBayes



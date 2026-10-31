-- Prove2me | Definitions.Def_KallMayerSLP_ProbConstr_probFun
-- name    : KallMayerSLP_ProbConstr_probFun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:20.215142+00:00
-- url     : https://prove2.me/theorems/5e9ad153-2a33-4100-8808-c1dde4ecb45e
-- title:
--   The probability function $G(x)=\mathbb P_\xi(T(\xi)x\ge h(\xi))$
-- statement:
--   Let $\mathbb P_\xi$ be the distribution of the random vector $\xi$ on $\mathbb R^r$ with its Borel $\sigma$-algebra $\mathcal B^r$. The (joint) probability function is
--   $$
--   G(x)=\mathbb P_\xi\big(T(\xi)x\ge h(\xi)\big)=\mathbb P_\xi(S(x)),\qquad x\in\mathbb R^n .
--   $$
--   It is the left-hand side of the probability (chance) constraint $G(x)\ge\alpha$.
--
--   **Formalization Note** The distribution is a measure $\mu$ on `Fin r → ℝ` and $G(x)$ is the real number `(μ (S x)).toReal`. The theorems assume $\mu$ is a probability measure, for which this is exact; where an event $S(x)$ must be Borel the theorems assume the data measurable.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Chapter 2, §2.1, p.96 (PDF 106)

import Mathlib
import Definitions.Def_KallMayerSLP_ProbConstr_feasibleEvent

open Matrix MeasureTheory

namespace KallMayerSLP.ProbConstr

/-- The (joint) probability function `G(x) = ℙ_ξ(T(ξ)x ≥ h(ξ)) = ℙ_ξ(S(x))`, where `μ` is the
distribution `ℙ_ξ` of the random vector `ξ` on `(ℝ^r, 𝓑^r)`.

Kall & Mayer 2005, Chapter 2, §2.1, p.96 (PDF 106).

**Formalization Note.** `μ` is a measure on `Fin r → ℝ` with its Borel σ-algebra; the theorems
assume `IsProbabilityMeasure μ`, under which `ENNReal.toReal` loses nothing (the value lies in
`[0, 1]`). For a non-measurable event `S(x)` Lean would return the outer measure; the theorems
that need `S(x)` to be an event assume the data measurable. -/
noncomputable def probFun {r m n : ℕ} (μ : Measure (Fin r → ℝ))
    (T : (Fin r → ℝ) → Matrix (Fin m) (Fin n) ℝ) (h : (Fin r → ℝ) → Fin m → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  (μ (feasibleEvent T h x)).toReal

end KallMayerSLP.ProbConstr



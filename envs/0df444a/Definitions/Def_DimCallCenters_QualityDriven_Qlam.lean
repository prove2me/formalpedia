-- Prove2me | Definitions.Def_DimCallCenters_QualityDriven_Qlam
-- name    : DimCallCenters_QualityDriven_Qlam
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:55:23.759563+00:00
-- url     : https://prove2.me/theorems/89f6a974-7a52-4b72-b287-6a025c054e91
-- title:
--   Stirling-type approximation $Q_\lambda(x)$ of the delay probability
-- statement:
--   For a service rate $\mu > 0$, an arrival rate $\lambda > 0$ and $x > 0$, let $N_\lambda(x) = \lambda/\mu + x\sqrt{\lambda/\mu}$ and
--
--   $$
--   r_\lambda(x) = \frac{\lambda/\mu}{N_\lambda(x)} \in (0,1).
--   $$
--
--   Section 4 defines
--
--   $$
--   Q_\lambda(x) = \frac{\exp\bigl\{N_\lambda(x)\,[\,1 - r_\lambda(x) + \log r_\lambda(x)\,]\bigr\}}{\sqrt{2\pi N_\lambda(x)}\,\bigl(1 - r_\lambda(x)\bigr)} .
--   $$
--
--   It approximates the delay probability $\pi_\lambda(x)$ when $x$ grows with $\lambda$ (Lemma 4.2), and it is the delay term of the surrogate cost in the quality-driven regime (Theorem 7.1).
--
--   **Formalization Note** The file defines both $r_\lambda$ (`ratioLam`) and $Q_\lambda$ (`Qlam`). Outside $x > 0$ the logarithm, square root and division take Lean's default values; no statement of the mission evaluates $Q_\lambda$ there.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 15, Section 4, displays for $Q_\lambda(x)$ and $r_\lambda(x)$

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_servers

namespace DimCallCenters.QualityDriven

/-- The load ratio `r_λ(x) = (λ/μ) / N_λ(x)` of Section 4, p. 15. For `λ, μ > 0` and `x > 0` it
lies in `(0, 1)`. -/
noncomputable def ratioLam (μ lam x : ℝ) : ℝ :=
  (lam / μ) / DimCallCenters.Rationalized.servers μ lam x

/-- The Stirling-type approximation of the delay probability of Section 4, p. 15:
`Q_λ(x) = exp{N_λ(x) [1 - r_λ(x) + log r_λ(x)]} / (√(2π N_λ(x)) (1 - r_λ(x)))`.
Meaningful for `x > 0` (with `λ, μ > 0`), where `0 < r_λ(x) < 1`. -/
noncomputable def Qlam (μ lam x : ℝ) : ℝ :=
  Real.exp (DimCallCenters.Rationalized.servers μ lam x * (1 - ratioLam μ lam x + Real.log (ratioLam μ lam x))) /
    (Real.sqrt (2 * Real.pi * DimCallCenters.Rationalized.servers μ lam x) * (1 - ratioLam μ lam x))

end DimCallCenters.QualityDriven



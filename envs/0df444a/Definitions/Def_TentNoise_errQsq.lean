-- Prove2me | Definitions.Def_TentNoise_errQsq
-- name    : TentNoise_errQsq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:44:45.737888+00:00
-- url     : https://prove2.me/theorems/14b6080f-d6cc-48d1-b37f-9254b97f0e03
-- title:
--   Rollout error $\varepsilon_Q^2$ under $\mathbb Q^\sigma_T$
-- statement:
--   The **rollout error** of $g$ along the noised fitted path $(Y_0,\dots,Y_T)\sim\mathbb Q^\sigma_T$ is
--
--   $$
--   \varepsilon_Q^2:=\frac1T\sum_{t=0}^{T-1}\mathbb E_{\mathbb Q^\sigma_T}\,|f(Y_t)-g(Y_t)|^2 .
--   $$
--
--   It measures the fitting error where the rollout actually goes, rather than under $\mu$; the KL bound of Lemma A.8 is stated with it.
--
--   **Formalization Note** Valued in $[0,\infty]$: each expectation is the lower Lebesgue integral of the nonnegative integrand, so no integrability condition is needed. The factor $1/T$ is $T^{-1}$ in $[0,\infty]$; the paper uses $T\ge1$.
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), §2.4, p.5 (PDF p.5), eq. (10)

import Mathlib
import Definitions.Def_TentNoise_noisedLaw

open MeasureTheory ProbabilityTheory TeschlODE.Shared
open scoped ENNReal

namespace TentNoise

/-- The rollout error `ε_Q² := (1/T) ∑_{t=0}^{T−1} E_{ℚ^σ_T} |f(Y_t) − g(Y_t)|²`
(Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), §2.4, p.5, eq. (10)), where `(Y₀, …, Y_T) ∼ ℚ^σ_T = ℚ^{g,σ}_T`.

**Formalization Note** Valued in `[0, ∞]`: each expectation is the lower Lebesgue integral of the
nonnegative integrand, so no integrability side condition is needed. Time `t = 0, …, T − 1` is the
coordinate `Fin.castSucc t` for `t : Fin T`. The factor `1/T` is `(T : ℝ≥0∞)⁻¹`; the paper has
`T ≥ 1` (at `T = 0` the empty sum makes the value `0`). -/
noncomputable def errQsq (g : ℝ → ℝ) (hg : Measurable g) (σ : ℝ) (T : ℕ) : ℝ≥0∞ :=
  (T : ℝ≥0∞)⁻¹ * ∑ t : Fin T,
    ∫⁻ p, ENNReal.ofReal ((tentMap 2 (p t.castSucc) - g (p t.castSucc)) ^ 2) ∂(noisedLaw g hg σ T)

end TentNoise



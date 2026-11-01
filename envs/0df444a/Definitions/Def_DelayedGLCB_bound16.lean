-- Prove2me | Definitions.Def_DelayedGLCB_bound16
-- name    : DelayedGLCB_bound16
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:25:08.400652+00:00
-- url     : https://prove2.me/theorems/658d8d82-9729-4856-8cbd-b374c0028689
-- title:
--   The right-hand side of the regret bound (16)
-- statement:
--   For parameters $\mu,M,\sigma,q,\hat\sigma,\kappa,L_g$, dimension $d$, horizon $T$, confidence level $\delta$ and exploration length $\tau$, with $\sigma_G=\sigma\sqrt{2+q}$ and $C_3=2\sigma^2+1$, the quantity $B_{16}$ is
--   $$
--   \begin{aligned}
--   B_{16}=\tau+L_g\Big[&4\sqrt{\mu+M}\sqrt{Td\log(T/d)}+2^{7/4}\sqrt{\sigma_G}(\log T)^{1/4}\sqrt{d\log(T/d)\,T}+\frac{2d\hat\sigma}{\kappa}\log\Big(\frac{T}{d\delta}\Big)\sqrt T\\
--   &+2\sqrt{2Td\log(T/d)}\Big(\sqrt{\sigma_G}\Big(2\log\frac1\delta+2\log C_3\,\sigma_G\sqrt{2\log T}+2\log C_3\Big)^{1/4}+\sqrt{1+2\sigma_G^2\log C_3}\Big)\Big].
--   \end{aligned}
--   $$
--
--   This is the high-probability regret bound of Theorem 1, of order $d\sqrt T\log T+\sqrt{(\mu+M)dT\log T}+\sqrt{\sigma_G}(\log T)^{3/4}\sqrt{dT}$.
--
--   **Formalization Note** Logarithms are natural and the fourth roots are real powers. On the domain $1\le d\le T$, $0<\delta<1$, $q\ge0$, $\sigma>0$, $\mu+M\ge0$ every logarithm is of a number at least $1$ and every radicand is nonnegative.
-- source:
--   Blanchet, Xu, Zhou, Delay-Adaptive Learning in Generalized Linear Contextual Bandits, arXiv:2003.05174v1, Theorem 1, (16), p.10

import Mathlib
import Definitions.Def_DelayedGLCB_TailEnvelope

namespace DelayedGLCB

/-- **The right-hand side of the regret bound (16).**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, Theorem 1, (16), p.10:

`τ + L_g [ 4√(µ+M) √(T d log(T/d)) + 2^{7/4} √σ_G (log T)^{1/4} √(d log(T/d) T)
  + (2dσ̂/κ) log(T/(dδ)) √T
  + 2√(2Td log(T/d)) ( √σ_G (2 log(1/δ) + 2 log C₃ σ_G √(2 log T) + 2 log C₃)^{1/4}
  + √(1 + 2σ_G² log C₃) ) ]`,

with `σ_G = σ√(2+q)` and `C₃ = 2σ² + 1` (p.8).

**Formalization Note.** All logarithms are natural; `(·)^{1/4}` and `2^{7/4}` are real powers. On the
domain of Theorem 1 (`1 ≤ d ≤ T`, `0 < δ < 1`, `q ≥ 0`, `σ > 0`, `µ + M ≥ 0`) every logarithm is of a
number `≥ 1` and every radicand and base is nonnegative. -/
noncomputable def bound16 (μ M σ q σhat κ Lg : ℝ) (d T : ℕ) (δ : ℝ) (τ : ℕ) : ℝ :=
  let sG := sigmaG σ q
  let L := Real.log ((T : ℝ) / d)
  (τ : ℝ) + Lg *
    (4 * Real.sqrt (μ + M) * Real.sqrt (T * d * L)
      + 2 ^ ((7 : ℝ) / 4) * Real.sqrt sG * Real.log T ^ ((1 : ℝ) / 4) * Real.sqrt (d * L * T)
      + 2 * d * σhat / κ * Real.log (T / (d * δ)) * Real.sqrt T
      + 2 * Real.sqrt (2 * T * d * L) *
        (Real.sqrt sG * (2 * Real.log (1 / δ) + 2 * Real.log (C3 σ) * sG * Real.sqrt (2 * Real.log T)
            + 2 * Real.log (C3 σ)) ^ ((1 : ℝ) / 4)
          + Real.sqrt (1 + 2 * sG ^ 2 * Real.log (C3 σ))))

end DelayedGLCB



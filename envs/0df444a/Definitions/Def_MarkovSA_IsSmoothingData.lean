-- Prove2me | Definitions.Def_MarkovSA_IsSmoothingData
-- name    : MarkovSA_IsSmoothingData
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:05.236778+00:00
-- url     : https://prove2.me/theorems/21fbeffa-2815-419b-8f10-27f14307bf0d
-- title:
--   Smoothing data $(\|\cdot\|_s,L,\ell_{cs},u_{cs},\theta)$ of Appendix A
-- statement:
--   Given the contraction factor $\beta$, the tuple $(\|\cdot\|_s,L,\ell_{cs},u_{cs},\theta)$ is **admissible smoothing data** if
--
--   1. $\|\cdot\|_s$ is an $L$-smooth norm;
--   2. $\ell_{cs},u_{cs}>0$ and $\ell_{cs}\|x\|_s\le\|x\|_c\le u_{cs}\|x\|_s$ for all $x$;
--   3. $\theta>0$ and $\beta^2<\dfrac{1+\theta\ell_{cs}^2}{1+\theta u_{cs}^2}$.
--
--   Such data always exist on a finite-dimensional space. The constants $\varphi_1,\varphi_2,\varphi_3$ of Theorem 2.1 are computed from them.
--
--   **Formalization Note** Every admissible choice is allowed (reading R7); $\ell_{cs},u_{cs}$ need not be the tight equivalence constants. Page 24 prints $\ell_{cs}\|\cdot\|_c\le\|\cdot\|_c$ on the left, a misprint of $\ell_{cs}\|\cdot\|_s\le\|\cdot\|_c$ (see the uses on pp.30, 34).
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Appendix A, Notation, p.24

import Mathlib
import Definitions.Def_MarkovSA_IsSmoothNorm

namespace MarkovSA

/-- The **smoothing data** `(‖·‖_s, L, ℓ_cs, u_cs, θ)` of the Notation paragraph (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, Appendix A, p.24),
relative to the contraction factor `β`: `‖·‖_s` is an `L`-smooth norm (`IsSmoothNorm`);
`ℓ_cs, u_cs > 0` with `ℓ_cs‖·‖_s ≤ ‖·‖_c ≤ u_cs‖·‖_s`; and `θ > 0` with `β² < (1 + θℓ_cs²)/(1 + θu_cs²)`.

**Formalization Note.** Every such choice is admissible (reading R7); `ℓ_cs, u_cs` need not be tight.
Page 24 prints `ℓ_cs‖·‖_c ≤ ‖·‖_c ≤ u_cs‖·‖_s`; the left norm is a misprint of `‖·‖_s`, as the uses on pp.30, 34 show
(`ℓ_cs = d^{−1/p}` for `‖·‖_c = ‖·‖_∞`, `‖·‖_s = ‖·‖_p`, and `‖·‖_s² ≤ ‖·‖_c²/ℓ_cs²`). -/
def IsSmoothingData {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (s : E → ℝ) (L ℓ u θ β : ℝ) : Prop :=
  IsSmoothNorm s L ∧ 0 < ℓ ∧ 0 < u ∧ (∀ x, ℓ * s x ≤ ‖x‖ ∧ ‖x‖ ≤ u * s x) ∧ 0 < θ ∧
    β ^ 2 < (1 + θ * ℓ ^ 2) / (1 + θ * u ^ 2)

end MarkovSA



-- Prove2me | Definitions.Def_AvramDividend_Classical_TranslatedLaw
-- name    : AvramDividend_Classical_TranslatedLaw
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-29T02:46:12.405222+00:00
-- url     : https://prove2.me/theorems/eb84f739-2e2e-4086-8091-74f9a5f45c1e
-- title:
--   The translated law P_z of a spectrally negative Levy process and its running supremum, for the E_z of eq. (3.12)
-- statement:
--   The paper writes $\mathbf E_x$ for expectation under $P_x$, the law of the translate $x+X$ of the spectrally negative Levy process $X$ started at $0$, and reserves $\mathbf E=\mathbf E_0$ for the base law (section 2, p. 3). Proposition 1, eq. (3.12), compares $\mathbf E_x$ on the left with $\mathbf E_{x-a}$ on the right, so the two sides of that identity are computed under *different* measures, and a formalization that integrates both against the single base measure $P$ states the identity only at the boundary $x=a$.
--
--   This module supplies the translated law explicitly. For $z\in\mathbb R$ let $X^{z}_t=z+X_t$ be the translate of $X$ by $z$, let $S^{z}_t=\sup_{0\le s\le t}(X^{z}_s\vee0)$ be its running supremum, and let $Y^{z,+}_t=S^{z}_t-X^{z}_t$ be its reflection at the past supremum. Since $X_0=0$, one has $X^{z}_0=z$.
--
--   For a measurable set $A$ let $\mathbf P_z(A)=\mathbf P\{\omega\in A\}$; when $A$ is carried by the path functional $F$ of $X$, $\mathbf E_z[F]=\mathbf E[F(X^{z}_\cdot)]$. In this notation
--
--   $$
--   \mathbf E_{x-a}\Bigl[\int_0^{\tau_a}e^{-qt}\,dS_t\Bigr]=\int^\infty\Bigl[\int^{\mathrm{Ici}\,0}_{\tau_a^{x-a}}e^{-qt}\,\mathrm d S^{x-a}_t\Bigr]\,\mathrm d\mathbf P,
--   $$
--
--   the form in which the right-hand side of eq. (3.12) must be stated, with $\tau_a^{x-a}=\inf\{t\ge0:Y^{x-a,+}_t>a\}$ the drawdown stopping time for the translated process. Setting $z=0$ recovers the base law and the eq. (3.13) statement $\mathbf E[\int_0^{\tau_a}e^{-qt}\,dS_t]=W^{(q)}(a)/W^{(q)\prime}(a)$.
--
--   Note that $S^{z}_t=\max\{0,\,z+S_t\}$, so the translated running supremum is not the base running supremum unless $z=0$; and $\tau_a^{x-a}$ is likewise not $\tau_a$ unless $x=a$.
--
--   **Formalization Note.** `runningSup` is supplied by the parent reflection module. The translate is a pathwise shift, so no measure-theoretic construction of $P_z$ is required: the translate is applied inside the integrand and the outer integral remains with respect to the base measure $P$. All values are in $[0,\infty]$.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, section 2 on p. 3 (the family P_x) and Proposition 1 eq. (3.12) on p. 8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection

/-!
The translated law `P_z` of a spectrally negative Lévy process, and the running supremum and
drawdown of the translate, for the `E_z` notation of Proposition 1, eq. (3.12), of
Avram, Palmowski, Pistorius, arXiv:math/0702893v1, §2 (p. 3) and p. 8.

The paper writes `E_z` for expectation under `P_z`, the law of the translate `z + X`, and
reserves `E = E_0` for the base law. Proposition 1 compares `E_x` with `E_{x-a}`, so a
formalization that integrates both sides against the single base measure `P` states the
identity only at `x = a`. This module supplies the translate explicitly.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- The translate `X^z = z + X` of `X` by `z`, started at `X^z_0 = z` since `X_0 = 0`. -/
noncomputable def translatedProcess (X : SpectrallyNegativeLevy P 𝓕) (z : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  z + X.X t ω

/-- The running supremum of the translate, `S^z_t = sup_{0 ≤ s ≤ t} (X^z_s ∨ 0)`. Since
`S^z_t = max(0, z + S_t)`, this differs from the base running supremum unless `z = 0`. -/
noncomputable def runningSupTranslated (X : SpectrallyNegativeLevy P 𝓕) (z : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ⨆ s : Icc (0 : ℝ≥0) t, maxZero (translatedProcess X z s ω)

/-- The reflection at the past supremum of the translate, `Y^{z,+}_t = S^z_t - X^z_t`. -/
noncomputable def reflectedSupTranslated (X : SpectrallyNegativeLevy P 𝓕) (z : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  runningSupTranslated X z t ω - translatedProcess X z t ω

/-- The drawdown stopping time of the translate,
`tau^{z}_a = inf{t ≥ 0 : Y^{z,+}_t > a}`, in `[0, ∞]` (`inf ∅ = ∞`). This is the
`hat tau_a` of eq. (3.12) when the process is started at `z = x - a`, and it coincides with
the base-law `barrierRuinTime` only when `z = 0`, i.e. only when `x = a`. -/
noncomputable def translatedBarrierRuinTime (X : SpectrallyNegativeLevy P 𝓕) (z a : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : a < reflectedSupTranslated X z t ω), (t : ℝ≥0∞)

/-- `E_z[ ∫_0^{hat tau_a} e^{-qt} dS_t ]` with the expectation taken under the law of the
translate `z + X`, in `[0, ∞]`. The outer integral remains with respect to the base measure
`P`; the translate is applied inside the integrand. For `z = x - a` this is the right-hand
side of eq. (3.12), and for `z = 0` it is eq. (3.13). -/
noncomputable def translatedBarrierSupValue (X : SpectrallyNegativeLevy P 𝓕) (z a q : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ t in paymentTimes (translatedBarrierRuinTime X z a ω),
    ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure (runningSupTranslated X z) ω) ∂P

end AvramDividend.Classical



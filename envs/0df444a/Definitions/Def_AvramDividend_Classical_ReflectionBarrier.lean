-- Prove2me | Definitions.Def_AvramDividend_Classical_ReflectionBarrier
-- name    : AvramDividend_Classical_ReflectionBarrier
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-29T02:12:16.522731+00:00
-- url     : https://prove2.me/theorems/9d9c47eb-fbc4-42e5-ac51-1434c7bd9d10
-- title:
--   The barrier ruin time tau-hat of eq. (3.12): the first time the drawdown S - X exceeds the barrier
-- statement:
--   This module supplies the stopping time $\hat\tau_a$ of Proposition 1 (eq. (3.12)) of Avram, Palmowski and Pistorius, arXiv:math/0702893v1, p. 8, and the value carried by the running supremum up to it.
--
--   Write $S_t=\sup_{0\le s\le t}(X_s\vee0)$ for the running supremum and $Y^+_t=S_t-X_t$ for the process $X$ reflected at its past supremum. Proposition 1 reads, for $a>0$ and $x\in[0,a]$,
--
--   $$
--   \mathbf E_x\Bigl[\int_0^{\sigma_a}e^{-qt}\,dL^a_t\Bigr]=\mathbf E_{x-a}\Bigl[\int_0^{\hat\tau_a}e^{-qt}\,dS_t\Bigr]=\frac{W^{(q)}(x)}{W^{(q)\prime}(a)}.
--   $$
--
--   The second equality identifies the stopping time through the same-law statement in section 4, p. 12: the controlled process $V^a$ started from $x$ has the same law as $a-Y^+$ started from $a-x$. Its ruin time is therefore the first time $a-Y^+_t$ drops below zero, that is
--
--   $$
--   \hat\tau_a=\inf\{t\ge0:\ Y^+_t>a\}=\inf\{t\ge0:\ S_t-X_t>a\},
--   $$
--
--   the first time the drawdown $S_t-X_t$ exceeds the barrier level $a$. The subscript $x-a$ on $\mathbf E_{x-a}$ records the starting point of the translated law $P_{x-a}$; it is not an additive shift inside the stopping time. The value is $\mathbf E[\int_0^{\hat\tau_a}e^{-qt}\,dS_t]$, written with the same `paymentTimes` and `dividendMeasure` idiom as `dividendValue` so that the two are read alike.
--
--   Note that the related stopping time $\inf\{t\ge0:c+(S_t-X_t)<0\}$, obtained by translating $Y^+$ by a capital $c$, is degenerate for $c\ge0$: since $S_t\ge X_t$ on every path (the index $s=t$ lies in the supremum and $X_0=0$), the translated process is bounded below by $c$ and the infimum is $+\infty$. The stopping time of eq. (3.12) is the reflection $a-Y^+$ above, not such a translate.
--
--   **Formalization Note.** `runningSup` and `dividendMeasure` are supplied by the parent reflection and dividend-strategy modules; the value is an extended nonnegative real in $[0,\infty]$. The module is purely definitional and asserts no fluctuation-theoretic property.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Proposition 1 eq. (3.12) on p. 8, together with the same-law statement in section 4 on p. 12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection

/-!
The barrier ruin time `τ̂ᵃ` of Proposition 1, eq. (3.12), of Avram, Palmowski and Pistorius,
arXiv:math/0702893v1, p. 8, together with the value carried by the running supremum up
to it.

`Definitions.Def_AvramDividend_Classical_Reflection` supplies `runningSup` and
`reflectedSup = runningSup - X`, i.e. the paper's `Y⁺ = S - X`.

Proposition 1 states, for `a > 0` and `x ∈ [0, a]`,

```
E_x[ ∫_0^{σ^a} e^{-qt} dL^a_t ] = E_{x-a}[ ∫_0^{τ̂ᵃ} e^{-qt} dS_t ] = W^{(q)}(x)/W^{(q)′}(a).
```

The stopping time `τ̂ᵃ` is identified by the same-law statement of section 4, p. 12: the
controlled process `V^a` started from `x` has the same law as `a - Y⁺` started from
`a - x`, so `τ̂ᵃ` is the first time `a - Y⁺` drops below zero, i.e.

```
τ̂ᵃ = inf{t ≥ 0 : Y⁺_t > a} = inf{t ≥ 0 : S_t - X_t > a},
```

the first time the drawdown `S_t - X_t` exceeds the barrier. The subscript `x - a` on
`E_{x-a}` records the starting point of the translated law `P_{x-a}`; it is *not* an
additive shift inside the stopping time.

Note that the translate `inf{t ≥ 0 : c + (S_t - X_t) < 0}` is degenerate for `c ≥ 0`:
since `S_t ≥ X_t` on every path, the translated process is bounded below by `c` and the
infimum is `⊤`. This module deliberately does *not* define that translate.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- The drawdown `S_t - X_t` of the paper, i.e. `Y⁺_t = reflectedSup X t`. -/
noncomputable def drawdown (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (ω : Ω) : ℝ :=
  reflectedSup X t ω

/-- The barrier ruin time `τ̂ᵃ = inf{t ≥ 0 : S_t - X_t > a}` of eq. (3.12), in `[0, ∞]`
(`inf ∅ = ∞`). This is the ruin time of `a - Y⁺` started from `a - x`, and it is finite
with positive probability, unlike the translate `inf{t : c + (S_t - X_t) < 0}` for `c ≥ 0`. -/
noncomputable def barrierRuinTime (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : a < drawdown X t ω), (t : ℝ≥0∞)

/-- `E[∫_0^{τ̂ᵃ} e^{-qt} dS_t]` for the stopping time of eq. (3.12), in `[0, ∞]`. Written with
the same `paymentTimes` / `dividendMeasure` idiom as `dividendValue`, so the two values are
read alike. -/
noncomputable def barrierSupValue (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ t in paymentTimes (barrierRuinTime X a ω),
    ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure (runningSup X) ω) ∂P

end AvramDividend.Classical



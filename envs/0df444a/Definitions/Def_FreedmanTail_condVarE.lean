-- Prove2me | Definitions.Def_FreedmanTail_condVarE
-- name    : FreedmanTail_condVarE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:07:20.823985+00:00
-- url     : https://prove2.me/theorems/59caa53f-320b-4a3b-89ee-dbafe326e457
-- title:
--   Conditional variance $\operatorname{Var}\{Y \mid \mathcal G\}$ with values in $[0, \infty]$
-- statement:
--   Let $(\Omega, \mathcal F, P)$ be a probability space, $\mathcal G \subseteq \mathcal F$ a sub-$\sigma$-field and $Y$ a real random variable, with no integrability assumed. Using conditional expectations of nonnegative functions (which always exist in $[0, \infty]$), define
--   $$\operatorname{Var}\{Y \mid \mathcal G\} = E\{Y^2 \mid \mathcal G\} - \big(E\{Y^+ \mid \mathcal G\} - E\{Y^- \mid \mathcal G\}\big)^2 ,$$
--   computed in $[0, \infty]$ with truncated subtraction. Where $E\{Y^2 \mid \mathcal G\} < \infty$ this is the usual conditional variance $E\{Y^2 \mid \mathcal G\} - (E\{Y \mid \mathcal G\})^2$; where $E\{Y^2 \mid \mathcal G\} = \infty$ it is $\infty$.
--
--   This is the paper's $V_n = \operatorname{Var}\{X_n \mid \mathcal F_{n-1}\}$, which may be infinite because the paper assumes only $X_n \le 1$.
--
--   **Formalization Note** Conditional expectations are Mathlib's conditional Lebesgue expectation $\mu^-[\,\cdot \mid \mathcal G]$. Since $y^- \le (1 + y^2)/2$, an infinite $E\{Y^- \mid \mathcal G\}$ forces $E\{Y^2 \mid \mathcal G\} = \infty$ almost surely, so the real-valued conversion of an infinite conditional mean never affects the value. Mathlib's real-valued `condVar`, which is $0$ outside $L^2$, is deliberately not used.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975) 100–118, doi:10.1214/aop/1176996452, §1, p. 101 ("Let V_n = Var{X_n | F_{n−1}}")

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace FreedmanTail

/-- **Conditional variance `Var{Y | 𝒢}` with values in `[0, ∞]`.**
Freedman, *On Tail Probabilities for Martingales*, Ann. Probab. 3 (1975) 100–118, §1, p. 101:
"Let V_n = Var{X_n | F_{n−1}}."

For a sub-σ-algebra `m`, a measure `μ` and a real random variable `Y`,
`condVarE m μ Y ω = E{Y² | m}(ω) − (E{Y⁺ | m}(ω) − E{Y⁻ | m}(ω))²`, computed in `ℝ≥0∞`
(truncated subtraction), where every conditional expectation is Mathlib's conditional Lebesgue
expectation `μ⁻[· | m]` of a nonnegative function, which needs no integrability.

**Formalization Note.** The paper places no integrability assumption on `X_n` (only `X_n ≤ 1`),
so `V_n` may be `+∞`. Where `E{Y² | m} < ∞` the value is the usual conditional variance
`E{Y² | m} − (E{Y | m})²` (nonnegative by conditional Jensen, so the truncation changes nothing);
where `E{Y² | m} = ∞` the value is `∞`. Since `y⁻ ≤ (1 + y²)/2`, `E{Y⁻ | m} = ∞` forces
`E{Y² | m} = ∞` a.e., so the `toReal` of an infinite conditional mean never affects the value.
Mathlib's real-valued `condVar` is deliberately not used: it is `0` outside `L²`. -/
noncomputable def condVarE {Ω : Type*} {mΩ : MeasurableSpace Ω} (m : MeasurableSpace Ω)
    (μ : Measure[mΩ] Ω) (Y : Ω → ℝ) : Ω → ℝ≥0∞ :=
  fun ω => μ⁻[fun ω => ENNReal.ofReal (Y ω ^ 2) | m] ω
    - ENNReal.ofReal (((μ⁻[fun ω => ENNReal.ofReal (Y ω) | m] ω).toReal
        - (μ⁻[fun ω => ENNReal.ofReal (- Y ω) | m] ω).toReal) ^ 2)

end FreedmanTail



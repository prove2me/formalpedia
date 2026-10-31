-- Prove2me | Definitions.Def_WasteNotWant_IsMarketLaw
-- name    : WasteNotWant_IsMarketLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:42:29.22323+00:00
-- url     : https://prove2.me/theorems/8fed60c1-2158-4675-8cf3-cfc41948c54f
-- title:
--   The law of the market size $Y$, with cdf $F$ on support $[a,b]$
-- statement:
--   The **market size** $Y$ is a random variable with cumulative distribution function $F$ on support $[a,b]$. We encode it by its law $\mu$, a probability measure on $\mathbb R$, and say that $\mu$ is a **market law on $[a,b]$** when
--
--   1. $0\le a<b$;
--   2. $\mu$ has no atoms, so that $F$ is continuous;
--   3. $\mu([a,b]^{\mathrm c})=0$;
--   4. $\mu((s,t))>0$ whenever $a\le s<t\le b$, so that $F$ is strictly increasing on $[a,b]$.
--
--   The cdf is $F(t)=\mu((-\infty,t])$, and an expectation $\mathbb E\,g(Y)$ is the integral $\int g\,d\mu$.
--
--   Every statement of this mission is made for an arbitrary market law. The uniform law on $[0,1]$ of the paper's Figure 2 is one example, and nothing here is restricted to it.
--
--   **Formalization Note** The paper writes "a cumulative probability distribution $F(\cdot)$ on support $[a,b]$". Items 1 and 2 are readings of that phrase: the paper characterizes optimal decisions by equations $F(\cdot)=\text{level}$ with levels in $(0,1)$, which need not have a solution when $F$ jumps, and $Y$ is a number of consumers. No integrability hypothesis appears, because every integrand in this mission is bounded on $[a,b]$.
-- source:
--   Long–Gui, Waste Not Want Not?, SSRN 4013877 (2023-08-10 copy), §3, p.8

import Mathlib

open MeasureTheory

namespace WasteNotWant

/-- **The law of the market size `Y`: a cumulative distribution function `F(·)` on support `[a, b]`.**
Long–Gui, *Waste Not Want Not?*, SSRN 4013877 (2023-08-10 copy), §3, p.8: "We refer to `Y` as the
market size and assume it is a random variable that follows a cumulative probability distribution
`F(·)` on support `[a,b]`."

`IsMarketLaw μ a b` says that the probability measure `μ` on `ℝ` is carried by `[a, b]`, charges
every open subinterval of `[a, b]`, and has no atoms, with `0 ≤ a < b`. The cdf `F` is
`ProbabilityTheory.cdf μ`, and `E g(Y)` is `∫ y, g y ∂μ`.

**Formalization Note.** The law `μ` replaces `F`; `F = cdf μ` is the same data. This predicate is a
reading of p.8. "Support `[a, b]`" is `μ [a, b]ᶜ = 0` and `0 < μ (s, t)` for `a ≤ s < t ≤ b`, so `F`
is strictly increasing on `[a, b]`. `NullSingletonClass μ` (no atoms) is continuity of `F`: the paper never says so, but
it characterizes optimal decisions by equations `F(·) = level` with levels in `(0, 1)`, which need
not have a solution at a jump of `F`. `0 ≤ a` because `Y` is a number of consumers, and `a < b`
because `a = b` would be an atom. Integrals of functions bounded on `[a, b]` are not junk, because
such functions are integrable under the bounded support; no integrability hypothesis is added. -/
structure IsMarketLaw (μ : Measure ℝ) (a b : ℝ) : Prop where
  /-- `Y` is a random variable: `μ` has total mass one. -/
  isProbabilityMeasure : IsProbabilityMeasure μ
  /-- `F` is continuous. -/
  nullSingleton : NullSingletonClass μ
  /-- The market size is nonnegative. -/
  a_nonneg : 0 ≤ a
  /-- The support is a nondegenerate interval. -/
  a_lt_b : a < b
  /-- `Y` lies in `[a, b]` almost surely. -/
  compl_Icc_null : μ (Set.Icc a b)ᶜ = 0
  /-- Every open subinterval of `[a, b]` has positive mass. -/
  Ioo_pos : ∀ s t : ℝ, a ≤ s → s < t → t ≤ b → 0 < μ (Set.Ioo s t)

end WasteNotWant



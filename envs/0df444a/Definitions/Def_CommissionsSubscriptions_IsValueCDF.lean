-- Prove2me | Definitions.Def_CommissionsSubscriptions_IsValueCDF
-- name    : CommissionsSubscriptions_IsValueCDF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:22:35.873739+00:00
-- url     : https://prove2.me/theorems/9a36772f-c078-42ed-8ffc-83b9822073e0
-- title:
--   Assumption 1 for a value distribution
-- statement:
--   An extended distribution function $F:\mathbb R\to\mathbb R$ satisfies **Assumption 1** if, writing $\bar v=F^{-1}(1)\in[0,\infty]$ for the upper end of its support:
--
--   1. $F$ is nondecreasing, $F(v)=0$ for $v\le0$, $F$ is continuous (the distribution is nonatomic), and $F(v)\to1$ as $v\to\infty$;
--   2. $F$ is continuously differentiable and strictly increasing on $(0,\bar v)$;
--   3. the mean is bounded: $\displaystyle\int_0^{\infty}\bigl(1-F(x)\bigr)\,dx<\infty$.
--
--   These are the paper's standing conditions on the sellers' and buyers' value distributions; under them $F$ is invertible on $(0,\bar v)$.
--
--   **Formalization Note** "A nonatomic distribution on $[0,\bar v]$ extended by $0$ and $1$" is exactly item 1. The paper's $\int_0^{\bar v}(1-F)$ equals $\int_0^\infty(1-F)$ because $1-F$ vanishes beyond $\bar v$; finiteness is stated as integrability of $1-F$ on $(0,\infty)$. $\bar v$ is computed from $F$ as `Finv F 1`.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), Assumption 1 and the extension of the domain to ℝ, p. 8; value distributions, p. 7

import Mathlib
import Definitions.Def_CommissionsSubscriptions_Finv

open Filter Topology

namespace CommissionsSubscriptions

/-- **Assumption 1 for one value distribution.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), §2 (value distributions `F : [0, v̄] → [0,1]`, p. 7),
Assumption 1 and the extension of the domain to `ℝ`, p. 8.

`F : ℝ → ℝ` is the extended CDF. With `v̄ := Finv F 1 ∈ [0, ∞]` (the upper end of the support):
1. `F` is monotone, `F v = 0` for `v ≤ 0`, `F` is continuous (nonatomic) and `F v → 1` as
   `v → ∞`;
2. `F` is strictly increasing and continuously differentiable on `(0, v̄)`;
3. bounded mean: `∫₀^∞ (1 − F(x)) dx < ∞`.

**Formalization Note (Reading 2).** "A nonatomic CDF on `[0, v̄]`, extended to `ℝ` by `0` on
`(−∞, 0]` and by `1` on `[v̄, ∞)`" is exactly item 1: monotone, zero on `(−∞,0]`, continuous, with
limit `1` at `+∞` (then `F = 1` on `[v̄, ∞)` and `F < 1` below `v̄`). The bounded-mean integral
`∫₀^{v̄} (1 − F)` equals `∫₀^∞ (1 − F)` because `1 − F` vanishes beyond `v̄`; it is stated as
integrability of `1 − F` on `(0, ∞)`. -/
def IsValueCDF (F : ℝ → ℝ) : Prop :=
  Monotone F ∧ (∀ v ≤ 0, F v = 0) ∧ Continuous F ∧ Tendsto F atTop (𝓝 1) ∧
    StrictMonoOn F {v : ℝ | 0 < v ∧ (v : EReal) < Finv F 1} ∧
    ContDiffOn ℝ 1 F {v : ℝ | 0 < v ∧ (v : EReal) < Finv F 1} ∧
    MeasureTheory.IntegrableOn (fun x => 1 - F x) (Set.Ioi 0)

end CommissionsSubscriptions



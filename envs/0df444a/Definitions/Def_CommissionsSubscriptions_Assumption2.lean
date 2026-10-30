-- Prove2me | Definitions.Def_CommissionsSubscriptions_Assumption2
-- name    : CommissionsSubscriptions_Assumption2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:23:52.391566+00:00
-- url     : https://prove2.me/theorems/58b3fc11-dc2c-4902-b41c-f2512acdff93
-- title:
--   Assumption 2: strict concavity of $uF^{-1}_{b_j}(1-u)$ and $-uF^{-1}_{s_i}(u)$
-- statement:
--   A market satisfies **Assumption 2** if, for every buyer type $j$ and seller type $i$,
--   $$u\mapsto u\,F^{-1}_{b_j}(1-u)\quad\text{and}\quad u\mapsto -u\,F^{-1}_{s_i}(u)$$
--   are strictly concave in $u\in[0,1]$.
--
--   For buyers this is the regularity of the value distribution familiar from mechanism design; for sellers it is the analogous condition on reservation values. It holds for uniform, exponential, generalized Pareto, Weibull and (truncated) normal distributions. Under it the function $h$ of (6) is concave, so (7) is a convex program.
--
--   **Formalization Note** The buyer function is stated on $[0,1]$ with value $0$ at $u=0$, which is footnote 4's convention $F^{-1}_{b_j}(1)\cdot0=0$. The seller function is stated on $[0,1)$: at $u=1$ its value is $-\bar v_{s_i}$, which is $-\infty$ for unbounded support; for bounded support the function is continuous at $1$ and strict concavity on $[0,1)$ is equivalent to strict concavity on $[0,1]$.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), Assumption 2, p. 12; footnote 4, p. 12

import Mathlib
import Definitions.Def_CommissionsSubscriptions_Market
import Definitions.Def_CommissionsSubscriptions_Finv

namespace CommissionsSubscriptions

/-- **Assumption 2.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), Assumption 2, p. 12:
"The functions `u F⁻¹_{b_j}(1 − u)` and `−u F⁻¹_{s_i}(u)` are strictly concave in `u ∈ [0,1]` for
all `i ∈ S` and for all `j ∈ B`."

**Formalization Note (Reading 3).** Buyers: strict concavity on the closed interval `[0,1]`. For
`u ∈ (0,1]` the argument `1 − u` is `< 1`, so `F⁻¹(1 − u)` is finite and `toReal` is exact; at
`u = 0` the value is `0 · toReal(F⁻¹(1)) = 0`, which is footnote 4's convention
(`F⁻¹(1)·0 = 0`, p. 12). Sellers: strict concavity on `[0,1)`. At `u = 1` the paper's value is
`−v̄_{s_i}`, which is `−∞` for unbounded support; for bounded support the function is continuous
at `1`, and a function continuous on `[0,1]` and strictly concave on `[0,1)` is strictly concave on
`[0,1]`, so the half-open reading is equivalent to the printed one in both cases. -/
def Assumption2 {S B : Type} (M : Market S B) : Prop :=
  (∀ j, StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun u : ℝ => u * (Finv (M.Fb j) (1 - u)).toReal)) ∧
    (∀ i, StrictConcaveOn ℝ (Set.Ico (0 : ℝ) 1)
      (fun u : ℝ => -u * (Finv (M.Fs i) u).toReal))

end CommissionsSubscriptions



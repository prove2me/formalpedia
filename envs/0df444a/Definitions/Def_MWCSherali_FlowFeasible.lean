-- Prove2me | Definitions.Def_MWCSherali_FlowFeasible
-- name    : MWCSherali_FlowFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:18.566876+00:00
-- url     : https://prove2.me/theorems/a6a511c6-6068-4d4c-ba8b-b91623648b0c
-- title:
--   Feasible solutions of the Flow LP
-- statement:
--   On $\Delta_{k,n}$ each terminal $a$ sends one unit of **commodity-$a$ flow** towards the opposite face $\{x_a=0\}$, moving only from $x$ to $x-\frac1ne_a+\frac1ne_i$ ($i\neq a$). A **feasible solution of (Flow-LP)** is a choice of flows $f_{a,x,i}\ge0$ ($x\in\Delta_{k,n}$, $a\in\operatorname{supp}(x)$, $i\neq a$) and capacities $b_{x,i}\ge0$ with
--
--   1. $f_{a,x,i}\le b_{x,i}$ for $x\in\Delta_{k,n}$, $i\in[k]$, $a\in\operatorname{supp}(x)\setminus\{i\}$;
--   2. for $x\in\Delta_{k,n}$ and $a\in\operatorname{supp}(x)$,
--   $$\sum_{i\neq a}f_{a,x,i}-\sum_{i\neq a,\ i\in\operatorname{supp}(x)}f_{a,\,x+\frac{e_a}n-\frac{e_i}n,\,i}=\mathbf 1[x=e_a].$$
--
--   Several commodities may share a capacity: one pays for the maximum, not the sum.
--
--   **Formalization Note** Flow values with $x_a=0$ or $i=a$ are not LP variables; they appear only in the condition $f\ge0$, which the value $0$ meets. The incoming flow at $x$ is written as a sum over the points $x'$ with $x'+e_i=x+e_a$ in integer coordinates (one such point if $x_i>0$, none otherwise).
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), (Flow-LP), p.23

import Mathlib
import Definitions.Def_MWCSherali_Grid
import Definitions.Def_MWCSherali_corner

namespace MWCSherali

/-- **Feasible solutions of (Flow-LP).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511
(version of Nov. 3, 2026), (Flow-LP), p.23: variables `f_{a,x,i} ≥ 0` (the commodity-`a` flow from
`x` to `x − e_a/n + e_i/n`, for `x ∈ Δ_{k,n}`, `a ∈ supp(x)`, `i ≠ a`) and capacities
`b_{x,i} ≥ 0` with
* `f_{a,x,i} ≤ b_{x,i}` for `x ∈ Δ_{k,n}`, `i ∈ [k]`, `a ∈ supp(x) ∖ {i}`;
* `∑_{i ≠ a} f_{a,x,i} − ∑_{i ≠ a, i ∈ supp(x)} f_{a, x + e_a/n − e_i/n, i} = 1[x = e_a]` for
  `x ∈ Δ_{k,n}`, `a ∈ supp(x)`.

**Formalization Note.**
* Points are integer coordinates (`Grid k n`), commodities and directions are `Fin k`
  (0-based). `f a x i` is `f_{a,x,i}`; `b x i` is `b_{x,i}`.
* `f` is a total function; its values with `x_a = 0` or `i = a` are not variables of the LP and
  enter no constraint except `0 ≤ f`, which they can meet with the value `0`.
* The incoming flow `f_{a, x + e_a/n − e_i/n, i}` for `i ∈ supp(x)` is written as the sum of
  `f a x' i` over the points `x'` with `x' + e_i = x + e_a` (integer coordinates): there is exactly
  one such `x'` when `x_i > 0` and none when `x_i = 0`. This avoids truncated subtraction. -/
def FlowFeasible (k n : ℕ) (f : Fin k → Grid k n → Fin k → ℝ) (b : Grid k n → Fin k → ℝ) :
    Prop :=
  (∀ a x i, 0 ≤ f a x i) ∧
  (∀ x i, 0 ≤ b x i) ∧
  (∀ (x : Grid k n) (i a : Fin k), a ≠ i → 0 < x.1 a → f a x i ≤ b x i) ∧
  (∀ (x : Grid k n) (a : Fin k), 0 < x.1 a →
    ∑ i ∈ Finset.univ.filter (· ≠ a), f a x i -
      ∑ i ∈ Finset.univ.filter (· ≠ a), ∑ x' : Grid k n,
        (if x'.1 + Pi.single i 1 = x.1 + Pi.single a 1 then f a x' i else 0) =
      if x = corner k n a then 1 else 0)

end MWCSherali



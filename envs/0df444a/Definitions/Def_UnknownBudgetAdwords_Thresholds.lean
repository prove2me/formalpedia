-- Prove2me | Definitions.Def_UnknownBudgetAdwords_Thresholds
-- name    : UnknownBudgetAdwords_Thresholds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:22:05.641892+00:00
-- url     : https://prove2.me/theorems/b5b61097-dbea-459b-a6b5-ae2f2195725a
-- title:
--   Critical thresholds $y^c_{i,\tau}$, truncated OPT moments, and $B(y)$
-- statement:
--   Fix a resource $i$, seeds $Y_{-i}$ for the others, and an allocation $\tau$ standing for OPT. The **base scenario** is $y_i=1$, where $i$ has bid price $0$ but stays available. The **critical threshold** of a moment $t+s$ is the value $y^c_{i,t+s}\in[0,1]$ with
--
--   $$
--   b_{i,t}\,(1-g(y^c_{i,t+s}))=\max_{j\in I(t+s,1)}b_{j,t}(1-g(y_j)),
--   $$
--
--   set to $0$ if no such value exists and to $1$ if $I(t+s,1)$ is empty.
--
--   The moments of $\mathrm{OPT}_i$ keep of each arrival $t$ matched to $i$ with positive bid the prefix $[t,t+c_t)$ of the fraction that fits in the budget,
--
--   $$
--   c_t=\min\Big\{1,\ \frac{(B_i-\text{assigned before }t)^+}{b_{i,t}}\Big\},
--   $$
--
--   so that $\sum_t b_{i,t}c_t=\mathrm{OPT}_i$. Sums over the set $V$ of distinct thresholds are sums over moments:
--
--   $$
--   \sum_{v\in V}b(v)F(v)=\sum_t b_{i,t}\int_0^{c_t}F(y^c_{i,t+s})\,ds,\qquad B(y)=\sum_{v\ge y,\ v\in V}b(v).
--   $$
--
--   These are the terms in which Lemmas 5 and 6 compare a run with the base scenario.
--
--   **Formalization Note** The printed $b(v)$ integrates over the whole of $[t,t+1)$, which contradicts $B(0)=\mathrm{OPT}_i$ and $B(y)\le B_i$ on the same pages whenever OPT's last bid overshoots the budget; the truncation is the correction. The definition of `yc` has three branches: if the base price $m$ is $0$ (which covers $I(\tau,1)=\emptyset$), the value is $1$; if $m\ge b_{i,t}(1-g(0))$, it is $0$; otherwise it is $1+\log(1-m/b_{i,t})/\beta$, whose logarithm has an argument above $g(0)>0$. For $b_{i,t}=0$ the printed value is not unique, and it does not matter, since then $c_t=0$. `sumV` is the sum over $V$ and `Bsum` is $B(y)$.
-- source:
--   Udwani, Adwords with Unknown Budgets and Beyond, arXiv:2110.00504v5, p.16 (OPT moments); p.17 (critical threshold, V, b(v), B(y)); p.11 (OPT_i)

import Definitions.Def_UnknownBudgetAdwords_FGPG
open MehtaOnlineAdAllocation.MSVV
open StochasticRewardMatching.Decomposable (Seeds)
noncomputable section

namespace UnknownBudgetAdwords

/-- The critical threshold `y^c_{i,τ}` at moment `τ = t + s` (Udwani, arXiv:2110.00504v5, p.17):
the value `y` with `b_{i,t} (1 − g(y)) = max_{j ∈ I(τ,1)} b_{j,t} (1 − g(y_j))`, where the right
side is `m`, the bid price `λ_τ` in the base scenario `y_i = 1`. It is `0` if no such value exists,
and `1` if `I(τ, 1)` is empty.

**Formalization Note** The three branches are: `m = 0` (which covers `I(τ, 1)` empty), value `1`;
`m ≥ b_{i,t} (1 − g(0))`, value `0`; otherwise the solution `1 + log(1 − m / b_{i,t}) / β`, where
`b_{i,t} > 0` and the argument of `log` exceeds `g(0) > 0`. For `b_{i,t} = 0` the printed value is
not unique, and it never matters: such an arrival has `cap = 0`. The value does not depend on
`Y i`. -/
def yc {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) (i : Fin N) (t : Fin M) (s : ℝ) : ℝ :=
  let m := lamAt I β (Function.update Y i 1) t s
  if m = 0 then 1
  else if I.bid i t * (1 - g β 0) ≤ m then 0
  else 1 + Real.log (1 - m / I.bid i t) / β

/-- The part of arrival `t` that counts as a moment of `OPT_i`, for the allocation `τ`: moments
`t + s` with `s < cap I τ i t` (Udwani, arXiv:2110.00504v5, p.16, corrected). This is
`min {1, (B_i − assigned before t) / b_{i,t}}`, clipped at `0`, when `τ` matches `t` to `i` with a
positive bid, and `0` otherwise.

**Formalization Note** The printed `b(v)` integrates over all of `[t, t + 1)`, which disagrees with
`B(0) = OPT_i` (p.17) and `B(y) ≤ B_i` (pp.18, 20) when the last bid of `OPT_i` overshoots the
budget, and Lemmas 5 and 6 then fail. Keeping only the part that fits gives
`∑ t, b_{i,t} cap_t = OPT_i`, the "total fraction of i's budget that is matched" of p.11. -/
def cap {N M : ℕ} (I : Instance N M) (τ : Allocation N M) (i : Fin N) (t : Fin M) : ℝ :=
  if τ t = some i ∧ 0 < I.bid i t then
    min 1 (max 0 ((I.budget i - assignedBefore I τ i t) / I.bid i t))
  else 0

/-- The sum `∑_{v ∈ V} b(v) F(v)` over the critical thresholds of the moments of `OPT_i`
(Udwani, arXiv:2110.00504v5, p.17), written over the moments themselves as
`∑_t b_{i,t} ∫_0^{cap_t} F(y^c_{i,t+s}) ds`.

**Formalization Note** The set `V` is finite, because `y^c` is piecewise constant in `s`; the
integral form says the same thing without a sum over a set whose finiteness would have to be
proved. -/
def sumV {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) (τ : Allocation N M) (i : Fin N)
    (F : ℝ → ℝ) : ℝ :=
  ∑ t, I.bid i t * ∫ s in (0 : ℝ)..cap I τ i t, F (yc I β Y i t s)

/-- `B(y) = ∑_{v ≥ y, v ∈ V} b(v)`: the cumulative bid on `i` from all moments of `OPT_i` with
critical threshold at least `y` (Udwani, arXiv:2110.00504v5, p.17). -/
def Bsum {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) (τ : Allocation N M) (i : Fin N)
    (y : ℝ) : ℝ :=
  sumV I β Y τ i (fun v => if y ≤ v then 1 else 0)

end UnknownBudgetAdwords



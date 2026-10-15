-- Prove2me | Definitions.Def_ApproxIC_Rounding_Setting
-- name    : ApproxIC_Rounding_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:39:53.863893+00:00
-- url     : https://prove2.me/theorems/f12406b8-c767-4b43-9e24-bd1baf632306
-- title:
--   §2, (P_ε), Assumption 1 — single-buyer ε-IC mechanism design: density on [0, v̄], mechanisms, IR, IC_ε, M(ε), Π, Π⋆
-- statement:
--   This file sets up the single-buyer, single-item selling problem of §2 of Balseiro, Besbes and Castro, *Mechanism Design under Approximate Incentive Compatibility*, in which the buyer is an $\varepsilon$-optimizer.
--
--   **The value distribution.** The buyer's value $v$ for the item is drawn from a distribution $F$ with a density $f$ supported in $S=[0,\bar v]$, where $\bar v>0$. The standing assumptions are:
--
--   1. $f(v)\ge 0$ for every $v$, and $f(v)=0$ for $v\notin[0,\bar v]$;
--   2. $f$ is integrable on $[0,\bar v]$ and $\int_0^{\bar v} f(v)\,dv = 1$.
--
--   The cumulative distribution function is $F(v)=\int_0^v f(u)\,du$.
--
--   **Mechanisms.** A direct mechanism $m=(x,t)$ consists of an allocation probability $x(v)$ and a payment $t(v)$ charged to a buyer who reports value $v$. It is *well formed* if $x(v)\in[0,1]$ for every $v\in S$ and $x$, $t$ are measurable. It is
--
--   1. **individually rational (IR)** if $v\cdot x(v)-t(v)\ge 0$ for all $v\in S$;
--   2. **$\varepsilon$-incentive compatible (IC$_\varepsilon$)** if
--   $$v\cdot x(v)-t(v)\;\ge\; v\cdot x(v')-t(v')-\varepsilon\qquad\text{for all } v,v'\in S.$$
--
--   Payments may be negative. $\mathcal M(\varepsilon)$ is the set of well-formed mechanisms satisfying IR and IC$_\varepsilon$; $\mathcal M(0)$ is the classical set of incentive compatible, individually rational mechanisms. The seller's revenue from $m$ is
--   $$\Pi(m)=\mathbb E_v[t(v)]=\int_0^{\bar v} t(v)\,f(v)\,dv,$$
--   and the optimal revenue under $\varepsilon$-IC is $\Pi^\star(\mathcal M(\varepsilon))=\sup_{m\in\mathcal M(\varepsilon)}\Pi(m)$.
--
--   These objects are the vocabulary of the paper's question: how much the optimal revenue $\Pi^\star(\mathcal M(\varepsilon))$ can exceed $\Pi^\star(\mathcal M(0))$.
--
--   **Formalization Note** All functions are total functions $\mathbb R\to\mathbb R$; every condition quantifies over $v\in[0,\bar v]$ only, and the revenue integral is over $[0,\bar v]$. Measurability of $x$ and $t$ is added so that $\mathbb E_v[t(v)]$ is meaningful; for a mechanism in $\mathcal M(\varepsilon)$, IR and IC$_\varepsilon$ make $t$ bounded on $S$, so the integral is a genuine one. $\bar v>0$ is implied by the page (a density on $[0,\bar v]$ with $0\le\bar v<\infty$). The bounded-variation half of Assumption 1 is not part of this file: Proposition 1 does not use it. $\Pi^\star$ is a `sSup`; the revenue image of $\mathcal M(\varepsilon)$ is nonempty (the zero mechanism) and bounded above by $\bar v$ (IR gives $t\le v\,x\le\bar v$ on $S$), so it is the true supremum.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), pp. 9–11, §2, problem (P_ε), M(ε), Π⋆(M(ε)), Assumption 1

import Mathlib

namespace ApproxIC.Rounding

open MeasureTheory

/-- The single-buyer model of §2 (Balseiro–Besbes–Castro, arXiv:2103.03403v2, pp. 9–11): the upper
end `vbar` (v̄) of the value support `S = [0, v̄]` and the density `f` of the buyer's value
distribution `F`. Every function is a total `ℝ → ℝ`; only its values on `S` matter. -/
structure Model where
  /-- The upper end v̄ of the support `S = [0, v̄]`. -/
  vbar : ℝ
  /-- The density `f` of the value distribution `F`. -/
  f : ℝ → ℝ

namespace Model

/-- The standing assumptions of §2 (the density half of Assumption 1, p. 11): `0 < v̄`, `f ≥ 0`,
`f` vanishes off `S = [0, v̄]`, `f` is integrable on `S`, and `∫_0^{v̄} f = 1`. -/
def Standing (M : Model) : Prop :=
  0 < M.vbar ∧
  (∀ v, 0 ≤ M.f v) ∧
  (∀ v ∉ Set.Icc 0 M.vbar, M.f v = 0) ∧
  IntegrableOn M.f (Set.Icc 0 M.vbar) ∧
  ∫ v in (0)..M.vbar, M.f v = 1

end Model

/-- The cumulative distribution function `F(v) = ∫_0^v f`. -/
noncomputable def cdf (M : Model) (v : ℝ) : ℝ := ∫ u in (0)..v, M.f u

/-- A direct mechanism `m = (x, t)`: allocation probability `x` and payment `t` as functions of
the reported value. -/
structure Mech where
  /-- The allocation probability `x(v)`. -/
  x : ℝ → ℝ
  /-- The payment `t(v)`. -/
  t : ℝ → ℝ

/-- Well-formedness of a mechanism in (P_ε), p. 10: `x : S → [0,1]`, `t : S → ℝ`, with `x` and `t`
measurable (needed for `E_v[t(v)]` to be meaningful; disclosed addition). -/
def IsMech (M : Model) (m : Mech) : Prop :=
  Measurable m.x ∧ Measurable m.t ∧ ∀ v ∈ Set.Icc 0 M.vbar, m.x v ∈ Set.Icc (0 : ℝ) 1

/-- Individual rationality (IR), p. 10: `v · x(v) − t(v) ≥ 0` for all `v ∈ S`. -/
def IR (M : Model) (m : Mech) : Prop :=
  ∀ v ∈ Set.Icc 0 M.vbar, 0 ≤ v * m.x v - m.t v

/-- ε-incentive compatibility (IC_ε), p. 10:
`v · x(v) − t(v) ≥ v · x(v′) − t(v′) − ε` for all `v, v′ ∈ S`. -/
def IC (M : Model) (ε : ℝ) (m : Mech) : Prop :=
  ∀ v ∈ Set.Icc 0 M.vbar, ∀ v' ∈ Set.Icc 0 M.vbar,
    v * m.x v' - m.t v' - ε ≤ v * m.x v - m.t v

/-- `M(ε)`, p. 11: the feasible mechanisms of (P_ε). -/
def Mset (M : Model) (ε : ℝ) : Set Mech :=
  {m | IsMech M m ∧ IR M m ∧ IC M ε m}

/-- The revenue `Π(m) = E_v[t(v)] = ∫_0^{v̄} t(v) f(v) dv`. -/
noncomputable def revenue (M : Model) (m : Mech) : ℝ :=
  ∫ v in (0)..M.vbar, m.t v * M.f v

/-- The optimal revenue `Π⋆(M(ε)) = sup_{m ∈ M(ε)} Π(m)`, p. 11. -/
noncomputable def optRev (M : Model) (ε : ℝ) : ℝ :=
  sSup (revenue M '' Mset M ε)

end ApproxIC.Rounding



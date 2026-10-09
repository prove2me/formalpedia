-- Prove2me | Definitions.Def_PrimalDualPricing_Regret_FluidValue
-- name    : PrimalDualPricing_Regret_FluidValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:20:02.747887+00:00
-- url     : https://prove2.me/theorems/4da1b14c-b694-4b75-b7a0-7fb38ceac4ff
-- title:
--   Eq. (2), p. 5 — the fluid value $J^D(T,c)$ and its scaled version $J^D_n(T,c)$
-- statement:
--   This file defines the fluid approximation (2) of the dynamic pricing problem and its scaled version.
--
--   Let $d_m$, $m=1,\dots,M$, be demand functions, $p_\infty$ the choke price, $c$ the inventory and $T$ the horizon. A price path $p(t)=(p_1(t),\dots,p_M(t))$ is **fluid feasible** if it is measurable, takes values in $[0,p_\infty]$ on $[0,T]$, and its total fluid demand does not exceed the inventory, that is $\sum_{m=1}^M\int_0^T d_m(p_m(t))\,dt\le c$. The **fluid value** is
--   $$J^D(T,c)=\sup\Big\{\sum_{m=1}^M\int_0^T p_m(t)\,d_m(p_m(t))\,dt\;:\;p\ \text{fluid feasible}\Big\},$$
--   the optimal value of (2). In the $n$-th system demand and inventory scale in proportion, $d_{m,n}=n\,d_m$ and $c_n=nc$ (p. 6), and
--   $$J^D_n(T,c)=J^D\text{ computed with demand } n\,d_m \text{ and inventory } nc.$$
--
--   $J^D_n$ is the benchmark in the regret $R^\pi_n=1-J^\pi_n/J^D_n$ of (6).
--
--   **Formalization Note** The maximum of (2) is written as a supremum. That it is attained by the constant path $p^*$, with $J^D=T\sum_m p^*_md_m(p^*_m)$, is Proposition 1.4, a separate item; it is not built into the definition.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 5, Eq. (2); pp. 6–7, scaled system d_{m,n} = n d_m, c_n = n c

import Mathlib

namespace PrimalDualPricing.Regret

open Set MeasureTheory

/-- A feasible path of the fluid problem (2) (Chen–Gallego, arXiv:1812.09234v3, p. 5): a measurable
price path `p : ℝ → Fin M → ℝ` (`p t m` is the type-`m` price at time `t`) with prices in the domain
`[0, p_∞]` on `[0, T]`, whose total fluid demand `∑_m ∫_0^T d_m(p_m(t)) dt` does not exceed the
inventory `c`. -/
def FluidFeasible {M : ℕ} (d : Fin M → ℝ → ℝ) (pinf c T : ℝ) (p : ℝ → Fin M → ℝ) : Prop :=
  Measurable p ∧ (∀ t ∈ Icc 0 T, ∀ m, p t m ∈ Icc 0 pinf) ∧
    ∑ m, ∫ t in (0 : ℝ)..T, d m (p t m) ≤ c

/-- The fluid value `J^D(T, c)` of (2) (p. 5):
`J^D(T, c) = max_{p(·)} ∑_m ∫_0^T p_m(t) d_m(p_m(t)) dt` subject to `∑_m ∫_0^T d_m(p_m(t)) dt ≤ c`,
the maximum over measurable price paths with values in `[0, p_∞]` (`FluidFeasible`), written as the
supremum of the attained revenues. -/
noncomputable def fluidValue {M : ℕ} (d : Fin M → ℝ → ℝ) (pinf c T : ℝ) : ℝ :=
  sSup ((fun p : ℝ → Fin M → ℝ => ∑ m, ∫ t in (0 : ℝ)..T, p t m * d m (p t m)) ''
    {p | FluidFeasible d pinf c T p})

/-- The fluid value of the `n`-th system, `J^D_n(T, c)` (pp. 6–7): demand `d_{m,n} = n d_m` and
inventory `c_n = n c`. -/
noncomputable def fluidValueN {M : ℕ} (d : Fin M → ℝ → ℝ) (pinf c T : ℝ) (n : ℕ) : ℝ :=
  fluidValue (fun m p => (n : ℝ) * d m p) pinf ((n : ℝ) * c) T

end PrimalDualPricing.Regret



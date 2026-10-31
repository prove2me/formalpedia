-- Prove2me | Definitions.Def_PushInfoShare_IsLinearSeparatingEq
-- name    : PushInfoShare_IsLinearSeparatingEq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:49.52597+00:00
-- url     : https://prove2.me/theorems/55d0bb46-9cdc-4ac8-ac1f-166ba7c51356
-- title:
--   Linear separating equilibrium of the stage game
-- statement:
--   Fix the sharing decisions $\delta$. A profile is a **linear separating equilibrium** if
--
--   1. each manufacturer that does not share has $B_i\neq0$, so that its price reveals its signal;
--   2. at all prices $w$ and signals $y$, the order $q(w,y)$ maximizes objective (2) over $\mathbb R^2$ at the retailer's forecast;
--   3. for each $i$, no measurable $f$ with $f\circ Y_i\in L^2$ yields a higher expected profit than the linear rule.
--
--   **Formalization Note** Optimality of the manufacturer is ex ante, over all $L^2$ pricing functions of $Y_i$, which amounts to optimality at almost every signal value. `δ i = true` means that $i$ shares.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), §3, p.9; §4, eqs. (2), (3), p.10

import Mathlib
import Definitions.Def_PushInfoShare_jointWeight
import Definitions.Def_PushInfoShare_retailerObjective
import Definitions.Def_PushInfoShare_forecast
import Definitions.Def_PushInfoShare_payoff

open MeasureTheory

namespace PushInfoShare

/-- `str` is a linear separating equilibrium of the stage game with sharing decisions `δ`, Jain,
SSRN:3388957 (PDF of 2021-04-25), §3–§4, pp.9–11, problems (2) and (3):

* separation: a manufacturer that does not share has `Bᵢ ≠ 0`, so its price reveals its signal;
* the retailer: at all prices `w` and signals `y`, `str.q · w y` maximizes objective (2) over
  `ℝ²` at the forecast computed from what the retailer knows and infers;
* the manufacturers: no measurable deviation `f(Yᵢ)` with `f ∘ Yᵢ ∈ L²` raises the expected profit.

**Formalization Note.** `δ i = true` means that `i` shares. Manufacturer optimality is ex ante, over
all `L²` pricing functions of `Yᵢ`, which is optimality at almost every signal value. Deviations
may use prices off the equilibrium path. Marginal costs are zero (p.7). -/
def IsLinearSeparatingEq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θ : Ω → ℝ)
    (Y : Fin 2 → Ω → ℝ) (σ a φ : ℝ) (δ : Fin 2 → Bool) (str : Profile) : Prop :=
  (∀ i, δ i = false → str.B i ≠ 0) ∧
  (∀ (w y q' : Fin 2 → ℝ),
    retailerObjective a φ (forecast (jointWeight μ θ Y σ) δ str w y) w q' ≤
      retailerObjective a φ (forecast (jointWeight μ θ Y σ) δ str w y) w
        (fun i => str.q i w y)) ∧
  (∀ (i : Fin 2) (f : ℝ → ℝ), Measurable f → MemLp (fun ω => f (Y i ω)) 2 μ →
    payoff μ Y str i f ≤ payoff μ Y str i fun y => str.α i + str.B i * y)

end PushInfoShare



-- Prove2me | Definitions.Def_RobustBooking_Shared_Noise
-- name    : RobustBooking_Shared_Noise
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T03:13:56.249585+00:00
-- url     : https://prove2.me/theorems/14d6d459-0ea9-4538-bd86-503ad952fb01
-- title:
--   Light-tailed i.i.d. demand shocks
-- statement:
--   The demand shocks $\varepsilon_1, \varepsilon_2, \dots$ are real random variables on a probability space $(\Omega, \mathbb{P})$. They are independent and identically distributed, with mean zero and variance $\sigma^2$ for some $\sigma > 0$. They are also light-tailed: there is a constant $z_0 > 0$ such that
--   $$\mathbb{E}\big[e^{z \varepsilon_t}\big] < \infty \quad \text{for all } |z| \le z_0 .$$
--
--   **Formalization Note.** `LightTailedNoise P ε σ` is a `Prop`-valued structure on a family `ε : ℕ → Ω → ℝ`. It requires measurability of each `ε t`, `iIndepFun ε P`, `IdentDistrib (ε t) (ε 0)`, `0 < σ`, membership in $L^2$, $\int \varepsilon_t \, d\mathbb{P} = 0$, $\int \varepsilon_t^2 \, d\mathbb{P} = \sigma^2$, and integrability of $e^{z\varepsilon_t}$ for $|z| \le z_0$. Period $t \ge 1$ uses `ε t`. The variable `ε 0` belongs to the i.i.d. family but is never used. No Gaussian assumption is made.
--
--   **Shared definition.** Serves Keskin–Zeevi 2014 chunks `02-sufficient-conditions` (previously `KeskinZeevi.SufficientConditions.Noise`) and `04-incumbent-sufficient-conditions` (previously `KeskinZeevi.IncumbentSufficient.Noise`); both cite the standing noise assumption of §2, p. 1144.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1144, Section 2

import Mathlib

open MeasureTheory ProbabilityTheory

namespace RobustBooking.Shared

/-- The demand shocks of §2 (Keskin–Zeevi 2014, p. 1144): `ε 0, ε 1, …` are measurable,
independent and identically distributed, with mean zero and variance `σ²` (`σ > 0`), and there is
`z₀ > 0` with `E[exp(z ε_t)] < ∞` for all `|z| ≤ z₀`. Period `t ≥ 1` uses `ε t`. -/
structure LightTailedNoise {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ε : ℕ → Ω → ℝ)
    (σ : ℝ) : Prop where
  measurable : ∀ t, Measurable (ε t)
  indep : iIndepFun ε P
  identDistrib : ∀ t, IdentDistrib (ε t) (ε 0) P P
  sigma_pos : 0 < σ
  memLp_two : ∀ t, MemLp (ε t) 2 P
  mean_zero : ∀ t, ∫ ω, ε t ω ∂P = 0
  variance_eq : ∀ t, ∫ ω, ε t ω ^ 2 ∂P = σ ^ 2
  exp_moment : ∃ z₀ : ℝ, 0 < z₀ ∧
    ∀ t (z : ℝ), |z| ≤ z₀ → Integrable (fun ω => Real.exp (z * ε t ω)) P

end RobustBooking.Shared



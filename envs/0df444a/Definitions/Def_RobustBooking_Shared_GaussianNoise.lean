-- Prove2me | Definitions.Def_RobustBooking_Shared_GaussianNoise
-- name    : RobustBooking_Shared_GaussianNoise
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T02:11:45.284336+00:00
-- url     : https://prove2.me/theorems/65080a7f-907b-4bdf-af46-9e14f3b1dde5
-- title:
--   i.i.d. N(0, σ²) demand shocks
-- statement:
--   On a probability space $(\Omega, \mathcal{F}, P)$, a sequence of real random variables $\varepsilon_1, \varepsilon_2, \dots$ is **i.i.d. Gaussian noise with variance $\sigma^2$** if each $\varepsilon_t$ is measurable, the family is mutually independent, and each $\varepsilon_t$ has law
--   $$\varepsilon_t \sim \mathcal{N}(0, \sigma^2).$$
--   This is the noise model the paper uses for its lower bounds (§3.1, p. 1145: "We use the case where $\epsilon_t \overset{\text{iid}}{\sim} \mathcal{N}(0,\sigma^2)$ to derive a lower bound on regret").
--
--   **Formalization Note.** Lean index $t$ is the paper's period $t+1$. The variance is passed as the nonnegative real $(\sigma^2)^+ = \sigma^2$.
--
--   **Shared definition.** Serves Keskin–Zeevi 2014 chunks `01-sqrt-lower-bound` (§3.1, p. 1145, noise of Theorem 1 and its lemmas, previously `KeskinZeevi.LowerBound.GaussianNoise`) and `03-incumbent-lower-bound` (§3.4, p. 1149, noise of Theorem 3, previously `KeskinZeevi.IncumbentLowerBound.GaussianNoise`); both pages state the same assumption $\epsilon_t \overset{\text{iid}}{\sim} \mathcal N(0,\sigma^2)$.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1145, Section 3.1

import Mathlib

namespace RobustBooking.Shared

open MeasureTheory ProbabilityTheory

/-- The demand shocks of §3.1 (p. 1145): on the probability space `(Ω, P)`, the random
variables `ε 0, ε 1, …` (the paper's `ε₁, ε₂, …`; Lean index `t` is period `t + 1`) are
measurable, mutually independent, and each has the Gaussian law `N(0, σ²)`. -/
structure GaussianNoise {Ω : Type*} [MeasurableSpace Ω] (σ : ℝ) (P : Measure Ω)
    (ε : ℕ → Ω → ℝ) : Prop where
  measurable : ∀ t, Measurable (ε t)
  indep : iIndepFun ε P
  law : ∀ t, P.map (ε t) = gaussianReal 0 (σ ^ 2).toNNReal

end RobustBooking.Shared



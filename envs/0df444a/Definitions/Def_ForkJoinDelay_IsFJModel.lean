-- Prove2me | Definitions.Def_ForkJoinDelay_IsFJModel
-- name    : ForkJoinDelay_IsFJModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:32.524588+00:00
-- url     : https://prove2.me/theorems/ea1167ee-9b92-4fc1-918f-53f58b4beaf1
-- title:
--   Exponential service times of the fork-join network
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\mu_0,\mu_1,\mu_2$ real numbers. Random variables $V_n,U_n,G_n:\Omega\to\mathbb R$, $n=0,1,2,\dots$, form a **fork-join service model** with rates $\mu_0,\mu_1,\mu_2$ if
--
--   1. every $V_n$, $U_n$, $G_n$ is measurable;
--   2. the whole family $\{V_n\}\cup\{U_n\}\cup\{G_n\}$ is mutually independent;
--   3. each $V_n$ is exponential with rate $\mu_0$, each $U_n$ exponential with rate $\mu_1$, each $G_n$ exponential with rate $\mu_2$.
--
--   $V_n$ are the service times at the first station $Q_0$, $U_n$ those at the upper fork-join station (UFJ) and $G_n$ those at the lower one (LFJ). The independence across the three families expresses that a customer's services at UFJ and LFJ are independent of each other and of $Q_0$.
--
--   **Formalization Note** By the memoryless property of the exponential law, the remaining service of a customer in service at the tagged customer's arrival is again exponential and independent of everything else, so a single i.i.d. family covers residual and fresh services. Mutual independence is one `iIndepFun` over the index set $\{0,1,2\}\times\mathbb N$.
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), §2, p.8 (exponential services with rates µ0, µ1, µ2; independent services at UFJ and LFJ); p.9 (residual service density µ0e^{−µ0t})

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ForkJoinDelay

/-- **The exponential service times of the fork-join network.**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, §2, p.8: "service times in the first part are exponentially
distributed with rate µ0"; the FJ stations have "exponential service times with rates µ1 and µ2
for the upper and lower stations"; customers join UFJ and LFJ "requiring independent services
at both stations".

`IsFJModel P μ₀ μ₁ μ₂ V U G` says that, under `P`, the random variables `V n` (services at the
first station `Q₀`), `U n` (services at the upper station UFJ) and `G n` (services at the lower
station LFJ), `n ∈ ℕ`, are measurable, **mutually independent as one family** (indexed by
`Fin 3 × ℕ`: station, then position), and exponentially distributed with rates `μ₀`, `μ₁`, `μ₂`
respectively.

**Formalization Note.** By the memoryless property (p.9: "the remaining service time of the
customer in service in Q0 has density µ0e^{−µ0t}"; p.10), the residual service times of the
customers in service at the arrival epoch of the tagged customer are again exponential and
independent of everything else, so one i.i.d. family serves for residual and fresh services
alike. `P` is a probability measure automatically, since `P.map (V 0)` is the probability
measure `expMeasure μ₀` for `μ₀ > 0`. -/
structure IsFJModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ₀ μ₁ μ₂ : ℝ)
    (V U G : ℕ → Ω → ℝ) : Prop where
  measurable_V : ∀ n, Measurable (V n)
  measurable_U : ∀ n, Measurable (U n)
  measurable_G : ∀ n, Measurable (G n)
  indep : iIndepFun (fun i : Fin 3 × ℕ => ![V, U, G] i.1 i.2) P
  law_V : ∀ n, P.map (V n) = expMeasure μ₀
  law_U : ∀ n, P.map (U n) = expMeasure μ₁
  law_G : ∀ n, P.map (G n) = expMeasure μ₂

end ForkJoinDelay



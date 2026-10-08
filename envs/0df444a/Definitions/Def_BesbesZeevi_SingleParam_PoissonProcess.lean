-- Prove2me | Definitions.Def_BesbesZeevi_SingleParam_PoissonProcess
-- name    : BesbesZeevi_SingleParam_PoissonProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T14:41:38.999147+00:00
-- url     : https://prove2.me/theorems/b0211190-2d35-433d-9e35-1a2f46705ddb
-- title:
--   Unit-rate Poisson process
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a measure space. A **unit-rate Poisson process** on it is a family of nonnegative integer random variables $N(t)$, $t\in\mathbb R$, such that
--
--   1. $N(0)=0$, and every sample path $t\mapsto N(t,\omega)$ is non-decreasing and right-continuous;
--   2. each $N(t)$ is measurable;
--   3. for $0\le s\le t$ the increment $N(t)-N(s)$ has the Poisson law with mean $t-s$;
--   4. for every finite strictly increasing sequence of times $0\le t_0<t_1<\dots<t_k$ the increments $N(t_1)-N(t_0),\dots,N(t_k)-N(t_{k-1})$ are mutually independent.
--
--   In the dynamic pricing model of Besbes and Zeevi, the cumulative demand under a price path $p(\cdot)$ is the time-changed process $N\big(\int_0^t\lambda(p(s))\,ds\big)$, so a single unit-rate process drives every policy.
--
--   **Formalization Note** Time is real; monotonicity and $N(0)=0$ force $N(t)=0$ for $t<0$, and only nonnegative times are used. The probability space is a parameter of the structure, so statements quantify over every such process. Statements that need $P$ to be a probability measure assume `IsProbabilityMeasure P` separately.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 7 (PDF p. 9), §3, eq. (1)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace BesbesZeevi.SingleParam

/-- A unit-rate Poisson counting process `N` on a measure space `(Ω, P)` (Besbes–Zeevi 2009,
p. 7: "Let `N(·)` be a unit rate Poisson process").

* `N 0 = 0`; every path `t ↦ N t ω` is non-decreasing and right-continuous;
* each `N t` is measurable;
* for `0 ≤ s ≤ t` the increment `N t - N s` has the Poisson law with mean `t - s`;
* for every finite strictly increasing sequence of times `0 ≤ t₀ < t₁ < … < t_k` the increments
  `N t_{i+1} - N t_i` are mutually independent.

Only nonnegative times are used by the pricing model; monotonicity together with `N 0 = 0`
forces `N t = 0` for `t < 0`. The probability space is a parameter, not a fixed construction. -/
structure PoissonProcess (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  /-- The counting process: `N t ω` is the number of points in `(0, t]`. -/
  N : ℝ → Ω → ℕ
  zero : ∀ ω, N 0 ω = 0
  mono : ∀ ω, Monotone (fun t => N t ω)
  rightCont : ∀ ω t, ContinuousWithinAt (fun s => (N s ω : ℝ)) (Set.Ici t) t
  meas : ∀ t, Measurable (N t)
  law : ∀ s t : ℝ, ∀ hst : s ≤ t, 0 ≤ s →
    P.map (fun ω => N t ω - N s ω) = poissonMeasure ⟨t - s, sub_nonneg.mpr hst⟩
  indep : ∀ (k : ℕ) (t : Fin (k + 1) → ℝ), 0 ≤ t 0 → StrictMono t →
    iIndepFun (fun (i : Fin k) (ω : Ω) => N (t i.succ) ω - N (t i.castSucc) ω) P

end BesbesZeevi.SingleParam



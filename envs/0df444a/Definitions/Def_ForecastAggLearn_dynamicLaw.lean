-- Prove2me | Definitions.Def_ForecastAggLearn_dynamicLaw
-- name    : ForecastAggLearn_dynamicLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:11.897223+00:00
-- url     : https://prove2.me/theorems/b53a72e2-e6ae-4114-96c3-d4bc41621981
-- title:
--   Law of $T$ periods of the dynamic environment
-- statement:
--   In the **dynamic environment** the evidence matrix $A$ is fixed while the information structure varies with time: period $t$ has prior $\mu_t$ and conditional signal laws $C_{t,j}^\omega$. The pairs $(\omega_t,s_t)$, $t=1,\dots,T$, are independent, and $(\omega_t,s_t)$ has the joint law $C_t$ of period $t$. This definition is the product law
--
--   $$
--   \bigotimes_{t=1}^T C_t
--   $$
--
--   on $(\Omega\times S_1\times\dots\times S_m)^T$.
--
--   **Formalization Note** Periods are `Fin T`, 0-based. The priors and laws are fixed sequences indexed by $\mathbb N$ (an oblivious environment); the signal spaces do not depend on $t$.
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §2, p.10

import Mathlib
import Definitions.Def_ForecastAggLearn_jointLaw

namespace ForecastAggLearn

open MeasureTheory

/-- **Law of the T-period dynamic environment.**
Babichenko, Garber, arXiv:1802.07107v1, §2, p.10: "In the dynamic environment the information
structure C varies over time, but A remains fixed. Namely the information structure along time is
a sequence (A, C_t)_t."

Period `t` draws `(ω_t, s_t)` from `jointLaw (μ t) (P t)`, independently across periods.

**Formalization Note.** Periods are `Fin T` (0-based; the paper's period `t ∈ [T]` is `t − 1`).
The priors `μ t` and conditional laws `P t` are fixed sequences (an oblivious environment); the
signal spaces `S j` do not depend on `t`. -/
noncomputable def dynamicLaw (T : ℕ) {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℕ → ℝ) (P : ℕ → (j : Fin m) → Bool → Measure (S j)) :
    Measure (Fin T → Bool × ((j : Fin m) → S j)) :=
  Measure.pi fun t : Fin T => jointLaw (μ t) (P t)

end ForecastAggLearn



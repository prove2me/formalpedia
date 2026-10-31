-- Prove2me | Definitions.Def_ForecastAggLearn_barL
-- name    : ForecastAggLearn_barL
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:39.828336+00:00
-- url     : https://prove2.me/theorems/133f4501-cac1-4f2a-bb07-fd9a2addffef
-- title:
--   Per-period logistic loss $\overline L_t(h)$, eq. (4)
-- statement:
--   For a vector $\tilde z\in\mathbb R^n$, a number $\tilde\mu\in\mathbb R$ and a state $\omega\in\{0,1\}$, the loss of an aggregation vector $h\in\mathbb R^n$ is
--
--   $$
--   \overline L(h)=(1-\omega)(h\cdot\tilde z+\tilde\mu)+\ln\bigl(1+\exp(-h\cdot\tilde z-\tilde\mu)\bigr).
--   $$
--
--   With $\tilde z=\tilde z_t$, $\tilde\mu=\tilde\mu_t$ and $\omega=\omega_t$ this is the loss $\overline L_t$ of eq. (4): the log loss of the forecast $(1+\exp(-h\cdot\tilde z_t-\tilde\mu_t))^{-1}$ when the state is $\omega_t$. It is convex in $h$, which is what online gradient descent needs.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin n)`, and $h\cdot\tilde z$ is the inner product. $1-\omega$ is `if ω then 0 else 1`.
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §4.2.1, eq. (4), p.18

import Mathlib

namespace ForecastAggLearn

/-- **The per-period loss `L̄_t` of an aggregation vector.**
Babichenko, Garber, arXiv:1802.07107v1, §4.2.1, eq. (4), p.18:
"L̄_t(h) := (1 − ω_t)(h · z̃_t + µ̃_t) + ln(1 + exp(−h · z̃_t − µ̃_t))."

`barL z μt ω h` with `z = z̃_t ∈ ℝⁿ`, `μt = µ̃_t ∈ ℝ` and state `ω = ω_t`.

**Formalization Note.** `ω` is `Bool` (`true` is ω = 1), so `1 − ω` is `if ω then 0 else 1`.
Vectors live in `EuclideanSpace ℝ (Fin n)` and `h · z̃` is the inner product. -/
noncomputable def barL {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) (μt : ℝ) (ω : Bool)
    (h : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (if ω then 0 else 1) * (inner ℝ h z + μt) + Real.log (1 + Real.exp (-(inner ℝ h z) - μt))

end ForecastAggLearn



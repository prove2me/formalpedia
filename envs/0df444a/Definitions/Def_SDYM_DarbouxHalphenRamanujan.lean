-- Prove2me | Definitions.Def_SDYM_DarbouxHalphenRamanujan
-- name    : SDYM_DarbouxHalphenRamanujan
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T01:22:23.28478+00:00
-- url     : https://prove2.me/theorems/02f2c8e1-9879-413f-9a40-8fd76c9ddc24
-- title:
--   The Darboux–Halphen systems and Ramanujan's differential system
-- statement:
--   Four predicates for the first-order systems appearing in the Darboux–Halphen reduction of the self-dual Yang–Mills equations, and in Ramanujan's 1916 work on Eisenstein series.
--
--   The **classical Darboux–Halphen system** (eq. (52) with $\tau^2 = 0$) is
--
--   $$\dot\omega_1 = \omega_2\omega_3 - \omega_1(\omega_2+\omega_3),\qquad \dot\omega_2 = \omega_3\omega_1 - \omega_2(\omega_3+\omega_1),\qquad \dot\omega_3 = \omega_1\omega_2 - \omega_3(\omega_1+\omega_2).$$
--
--   The **generalized Darboux–Halphen system** (eqs. (52)–(53)) adds $\tau^2 = \tau_1^2+\tau_2^2+\tau_3^2$ to each right-hand side and couples in the three equations $\dot\tau_1 = -\tau_1(\omega_2+\omega_3)$, $\dot\tau_2 = -\tau_2(\omega_3+\omega_1)$, $\dot\tau_3 = -\tau_3(\omega_1+\omega_2)$. In the Lean text the $\tau_i$ are written $x_i$ to keep them apart from the independent variable.
--
--   **Ramanujan's system in the nome $q$** (eq. (78)) is
--
--   $$q\frac{dP}{dq} = \frac{P^2-Q}{12},\qquad q\frac{dQ}{dq} = \frac{PQ-R}{3},\qquad q\frac{dR}{dq} = \frac{PR-Q^2}{2},$$
--
--   written with the derivatives $dP/dq, dQ/dq, dR/dq$ as explicit companion functions and the factor $q$ kept on the left, so that no division by $q$ occurs and the origin needs no special treatment.
--
--   **Ramanujan's system in the additive variable $\tau$** (eq. (79)), obtained from the previous one by $q = e^{2i\tau}$, is
--
--   $$\frac{dP}{d\tau} = \frac{i}{6}(P^2-Q),\qquad \frac{dQ}{d\tau} = \frac{2i}{3}(PQ-R),\qquad \frac{dR}{d\tau} = i(PR-Q^2).$$
-- source:
--   M. J. Ablowitz, S. Chakravarty, R. G. Halburd, "Integrable systems and reductions of the self-dual Yang-Mills equations", J. Math. Phys. 44 (2003) 3147-3173, https://doi.org/10.1063/1.1586967, Sec. V p. 3165 Eqs. (52)-(53), and Sec. V.A p. 3170 Eqs. (78)-(79)

import Mathlib

namespace SDYM

/-- The classical Darboux–Halphen system, Ablowitz–Chakravarty–Halburd eq. (52) with
`τ² = 0`:
`ω₁' = ω₂ω₃ - ω₁(ω₂ + ω₃)`, and its two cyclic images. -/
def IsClassicalDHSolution (s : Set ℂ) (w₁ w₂ w₃ : ℂ → ℂ) : Prop :=
  (∀ t ∈ s, HasDerivAt w₁ (w₂ t * w₃ t - w₁ t * (w₂ t + w₃ t)) t) ∧
  (∀ t ∈ s, HasDerivAt w₂ (w₃ t * w₁ t - w₂ t * (w₃ t + w₁ t)) t) ∧
  (∀ t ∈ s, HasDerivAt w₃ (w₁ t * w₂ t - w₃ t * (w₁ t + w₂ t)) t)

/-- The generalized Darboux–Halphen system, Ablowitz–Chakravarty–Halburd eqs. (52)–(53),
with `τ² = τ₁² + τ₂² + τ₃²`:
`ω₁' = ω₂ω₃ - ω₁(ω₂ + ω₃) + τ²` (and cyclic), together with
`τ₁' = -τ₁(ω₂ + ω₃)` (and cyclic).
Here `x₁, x₂, x₃` denote `τ₁, τ₂, τ₃`. -/
def IsGeneralizedDHSolution (s : Set ℂ) (w₁ w₂ w₃ x₁ x₂ x₃ : ℂ → ℂ) : Prop :=
  (∀ t ∈ s, HasDerivAt w₁
    (w₂ t * w₃ t - w₁ t * (w₂ t + w₃ t) + (x₁ t ^ 2 + x₂ t ^ 2 + x₃ t ^ 2)) t) ∧
  (∀ t ∈ s, HasDerivAt w₂
    (w₃ t * w₁ t - w₂ t * (w₃ t + w₁ t) + (x₁ t ^ 2 + x₂ t ^ 2 + x₃ t ^ 2)) t) ∧
  (∀ t ∈ s, HasDerivAt w₃
    (w₁ t * w₂ t - w₃ t * (w₁ t + w₂ t) + (x₁ t ^ 2 + x₂ t ^ 2 + x₃ t ^ 2)) t) ∧
  (∀ t ∈ s, HasDerivAt x₁ (-(x₁ t) * (w₂ t + w₃ t)) t) ∧
  (∀ t ∈ s, HasDerivAt x₂ (-(x₂ t) * (w₃ t + w₁ t)) t) ∧
  (∀ t ∈ s, HasDerivAt x₃ (-(x₃ t) * (w₁ t + w₂ t)) t)

/-- Ramanujan's 1916 differential system in the nome `q`,
Ablowitz–Chakravarty–Halburd eq. (78):
`q dP/dq = (P² - Q)/12`, `q dQ/dq = (PQ - R)/3`, `q dR/dq = (PR - Q²)/2`.
The functions `Pd, Qd, Rd` are the `q`-derivatives of `P, Q, R`. -/
def IsRamanujanQSolution (s : Set ℂ) (P Q R Pd Qd Rd : ℂ → ℂ) : Prop :=
  (∀ q ∈ s, HasDerivAt P (Pd q) q) ∧
  (∀ q ∈ s, HasDerivAt Q (Qd q) q) ∧
  (∀ q ∈ s, HasDerivAt R (Rd q) q) ∧
  (∀ q ∈ s, q * Pd q = (P q ^ 2 - Q q) / 12) ∧
  (∀ q ∈ s, q * Qd q = (P q * Q q - R q) / 3) ∧
  (∀ q ∈ s, q * Rd q = (P q * R q - Q q ^ 2) / 2)

/-- Ramanujan's system in the additive variable `τ` (with `q = exp (2iτ)`),
Ablowitz–Chakravarty–Halburd eq. (79):
`dP/dτ = i(P² - Q)/6`, `dQ/dτ = 2i(PQ - R)/3`, `dR/dτ = i(PR - Q²)`. -/
def IsRamanujanTauSolution (s : Set ℂ) (P Q R : ℂ → ℂ) : Prop :=
  (∀ z ∈ s, HasDerivAt P (Complex.I * (P z ^ 2 - Q z) / 6) z) ∧
  (∀ z ∈ s, HasDerivAt Q (2 * Complex.I * (P z * Q z - R z) / 3) z) ∧
  (∀ z ∈ s, HasDerivAt R (Complex.I * (P z * R z - Q z ^ 2)) z)

end SDYM



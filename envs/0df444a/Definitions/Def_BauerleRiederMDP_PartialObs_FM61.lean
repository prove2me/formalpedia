-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_FM61
-- name    : BauerleRiederMDP_PartialObs_FM61
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:15.243658+00:00
-- url     : https://prove2.me/theorems/640a3d0c-95d7-4a0e-ab79-e8f15548ecac
-- title:
--   Assumption (FM) of Section 6.1
-- statement:
--   Let $R(y)$ denote a random vector with law $Q^R(\cdot\mid y)$. Assumption (FM) of Section 6.1 consists of:
--
--   1. **No arbitrage.** For all $y\in E_Y$ and $\varphi\in\mathbb R^d$: $\varphi\cdot R(y)\ge0$ a.s. implies $\varphi\cdot R(y)=0$ a.s.
--   2. **Common support.** The support of $R(y)$ does not depend on $y\in E_Y$.
--   3. **Moments.** $\sup_y\mathbb E\|R(y)\|<\infty$.
--
--   The second assumption guarantees that the support of $R_{n+1}$ does not depend on $Y_n$ and $n$.
--
--   **Formalization Note** The support of a law on $\mathbb R^d$ is the smallest closed set of full measure, so two laws have the same support exactly when they give measure zero to the same complements of closed sets; this is how 2. is stated. The sup norm is used in 3.; all norms on $\mathbb R^d$ are equivalent.
-- source:
--   Bäuerle & Rieder (2011), §6.1, Assumption (FM), p.176 (PDF 189)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **Assumption (FM) of §6.1.**
Bäuerle & Rieder (2011), §6.1, p.176 (PDF 189): "The following assumption on the financial market
is used throughout this section. Assumption (FM):
(i) There are no arbitrage opportunities in the market, i.e. for all `y ∈ E_Y` and `φ ∈ ℝ^d` it
holds: `φ · R(y) ≥ 0` IP-a.s. ⇒ `φ · R(y) = 0` IP-a.s.
(ii) The support of `R(y)` is independent of `y ∈ E_Y`.
(iii) `sup_y IE ‖R(y)‖ < ∞`."
Here `R(y)` is a random vector with law `Q^R(·|y)` (p.175).

**Formalization Note.** (ii): the support of a law on `ℝ^d` is the smallest closed set of full
measure, so two laws have the same support iff they give measure `0` to the same complements of
closed sets; this is how (ii) is stated. (iii): the norm on `Fin d → ℝ` is the sup norm; all norms
on `ℝ^d` are equivalent, so the finiteness condition is the book's. -/
structure FM61 {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d) : Prop where
  /-- (FM)(i): no arbitrage for every hidden state. -/
  noArbitrage : ∀ (y : EY) (φ : Fin d → ℝ), (∀ᵐ z ∂M.QR y, 0 ≤ φ ⬝ᵥ z) →
    ∀ᵐ z ∂M.QR y, φ ⬝ᵥ z = 0
  /-- (FM)(ii): the support of `R(y)` does not depend on `y`. -/
  support_indep : ∀ (y y' : EY) (F : Set (Fin d → ℝ)), IsClosed F →
    (M.QR y Fᶜ = 0 ↔ M.QR y' Fᶜ = 0)
  /-- (FM)(iii): `sup_y IE ‖R(y)‖ < ∞`. -/
  moment : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ y, ∫⁻ z, ‖z‖ₑ ∂M.QR y ≤ K

end BauerleRiederMDP.PartialObs



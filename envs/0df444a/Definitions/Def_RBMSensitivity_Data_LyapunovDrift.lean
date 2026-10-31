-- Prove2me | Definitions.Def_RBMSensitivity_Data_LyapunovDrift
-- name    : RBMSensitivity_Data_LyapunovDrift
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:38:21.89119+00:00
-- url     : https://prove2.me/theorems/833fbb68-ac11-45c3-8613-2f0aba0507e8
-- title:
--   The drift condition (7.5) on $U_0$
-- statement:
--   Constants $r_1,r_2\in(0,\infty)$, $\beta_0\in(0,1)$ and $\eta_0,\Delta_0,K_0\in(0,\infty)$ satisfy the **drift condition** on $U_0$ if
--   $$\mathbb E\big[V^\alpha(\Xi^{\alpha,\xi}(\Delta_0))\big]\le\beta_0V^\alpha(\xi)+K_0\mathbf 1\{\xi\in\mathbb X_{\Delta_0,\eta_0}\},\qquad\alpha\in U_0,\ \xi\in\mathbb X.$$
--
--   This is a geometric drift condition for the discrete skeleton of the joint process, uniform in $\alpha\in U_0$.
--
--   **Formalization Note** The expectation is taken as a Lebesgue integral with values in $[0,\infty]$, so the inequality includes finiteness of the left side.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Proposition 7.3, (7.5), p.28

import Mathlib
import Definitions.Def_RBMSensitivity_Data_V
import Definitions.Def_RBMSensitivity_Data_XSet
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The constants `r_1, r_2 ∈ (0, ∞)`, `β_0 ∈ (0, 1)`, `η_0, Δ_0, K_0 ∈ (0, ∞)` satisfy (7.5) on `U₀`:
arXiv:1907.00472v2, Proposition 7.3, p.28,
`E[V^α(Ξ^{α,ξ}(Δ_0))] ≤ β_0 V^α(ξ) + K_0 1{ξ ∈ X_{Δ_0,η_0}}` for `α ∈ U_0`, `ξ ∈ X`.

**Formalization Note.** The expectation is a Lebesgue integral in `ℝ≥0∞` of a nonnegative function, so
it is a true statement of finiteness. It cannot hold by a junk value of a Bochner integral. -/
def Data.LyapunovDrift {J : ℕ} {Ω : Type*} [MeasurableSpace Ω] (D : Data J) (B : ℝ → Set (E J))
    (P : Measure Ω) (Z : ℝ → E J → ℝ≥0 → Ω → E J) (𝒥 : ℝ → E J × E J → ℝ≥0 → Ω → E J)
    (U₀ : Set ℝ) (r₁ r₂ β₀ η₀ : ℝ) (Δ₀ : ℝ≥0) (K₀ : ℝ) : Prop :=
  0 < r₁ ∧ 0 < r₂ ∧ 0 < β₀ ∧ β₀ < 1 ∧ 0 < η₀ ∧ 0 < Δ₀ ∧ 0 < K₀ ∧
    ∀ α ∈ U₀, ∀ ξ ∈ D.X,
      ∫⁻ ω, ENNReal.ofReal (D.V B r₁ r₂ α (Z α ξ.1 Δ₀ ω, 𝒥 α ξ Δ₀ ω)) ∂P ≤
        ENNReal.ofReal (β₀ * D.V B r₁ r₂ α ξ +
          K₀ * (D.XSet U₀ Δ₀ η₀).indicator (fun _ => (1 : ℝ)) ξ)

end RBMSensitivity



-- Prove2me | Definitions.Def_SparseTensorInj_Certify_MomentParams
-- name    : SparseTensorInj_Certify_MomentParams
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:36:36.025489+00:00
-- url     : https://prove2.me/theorems/c2836bbb-563a-42f6-8674-ce7952d2a7b1
-- title:
--   The moment parameter $B_t$, $\rho_t=\sigma^2/B_t^2$ and the scaled sparse Rademacher law $D_t$ (eq. (10), Definition 62)
-- statement:
--   For $\sigma,\gamma>0$ and an integer $t\ge1$, eq. (10) sets $a=\log(1+\gamma^2/\sigma^2)$ and
--   $$B_t^2=C_0\big(\sigma^2+\gamma^2(t+a)\big),$$
--   where $C_0>0$ is a sufficiently large universal constant, and Definition 62 sets $\rho_t=\sigma^2/B_t^2\le1$. The **scaled sparse Rademacher law** $D_t$ is the law of
--   $$\xi=\begin{cases}+\rho_t^{-1/2}&\text{with probability }\rho_t/2,\\-\rho_t^{-1/2}&\text{with probability }\rho_t/2,\\0&\text{with probability }1-\rho_t,\end{cases}$$
--   so that $\mathbb E\xi^{2r}=\rho_t^{1-r}$ (Claim 63). These parameters drive Lemmas 49, 66, 69, 83 and Corollary 70.
--
--   **Formalization Note.** `Bsq C₀ σ γ t` is $B_t^2$ with $C_0$ an explicit argument; the statements quantify it as $\exists C_0^*>0,\ \forall C_0\ge C_0^*$. `sparseRademacher ρ` is the measure $\tfrac\rho2\delta_{\rho^{-1/2}}+\tfrac\rho2\delta_{-\rho^{-1/2}}+(1-\rho)\delta_0$, a probability measure for $\rho\in(0,1]$; $D_t$ is `sparseRademacher (rhoT C₀ σ γ t)`.
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 27, eq. (10); p. 36, Definition 62

import Mathlib

open MeasureTheory

namespace SparseTensorInj.Certify

/-- The variance-sensitive moment parameter of eq. (10) (p. 27): with `a = log(1 + γ^2/σ^2)`,
`B_t^2 = C_0 (σ^2 + γ^2 (t + a))`. The constant `C_0` ("a sufficiently large universal constant")
is an explicit argument; every statement using it quantifies `∃ C₀* > 0, ∀ C₀ ≥ C₀*`. -/
noncomputable def Bsq (C₀ σ γ : ℝ) (t : ℕ) : ℝ :=
  C₀ * (σ ^ 2 + γ ^ 2 * ((t : ℝ) + Real.log (1 + γ ^ 2 / σ ^ 2)))

/-- `ρ_t = σ^2 / B_t^2` (Definition 62, p. 36). -/
noncomputable def rhoT (C₀ σ γ : ℝ) (t : ℕ) : ℝ := σ ^ 2 / Bsq C₀ σ γ t

/-- The scaled sparse Rademacher law `D_t` of Definition 62 (p. 36), written for a parameter
`ρ ∈ (0, 1]`: `ξ = +ρ^{-1/2}` with probability `ρ/2`, `ξ = −ρ^{-1/2}` with probability `ρ/2`, and
`ξ = 0` with probability `1 − ρ`. The paper's `D_t` is `sparseRademacher (ρ_t)`. -/
noncomputable def sparseRademacher (ρ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (ρ / 2) • Measure.dirac (1 / Real.sqrt ρ) +
    ENNReal.ofReal (ρ / 2) • Measure.dirac (-(1 / Real.sqrt ρ)) +
    ENNReal.ofReal (1 - ρ) • Measure.dirac 0

end SparseTensorInj.Certify



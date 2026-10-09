-- Prove2me | Definitions.Def_ResidualsDRO_Unified_Assumptions
-- name    : ResidualsDRO_Unified_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:04:36.429271+00:00
-- url     : https://prove2.me/theorems/7457678c-40de-43b6-ad3a-c812adc9ee82
-- title:
--   Assumptions 9, 12, 13, 14, 15 — Lipschitz cost, shrinking probability set, ULLN, FCLT, regression rate
-- statement:
--   The assumptions of Theorem 17, at a fixed covariate realization $x$, in the notation of the Setting file.
--
--   1. **Assumption 9** (Lipschitz cost). For each $z\in\mathcal Z$, $c(z,\cdot)$ is Lipschitz continuous on $\mathcal Y$ with constant $L(z)\ge0$, and $\sup_{z\in\mathcal Z}L(z)<+\infty$.
--   2. **Assumption 12** (radius of the probability set). For constants $\rho>1$ and $C_\zeta>0$,
--   $$
--   \sup_{p\in\mathfrak P_n(x;\zeta_n(x))}\sum_{i=1}^n\Bigl(p_i-\frac1n\Bigr)^2=C_\zeta n^{-\rho}
--   $$
--   for all sufficiently large $n$.
--   3. **Assumption 13** (weak uniform LLN for the squared cost). $\sup_{z\in\mathcal Z}\mathbb E[c(z,f^*(x)+\varepsilon)^2]<+\infty$ and
--   $$
--   \sup_{z\in\mathcal Z}\Bigl|\frac1n\sum_{i=1}^n c(z,f^*(x)+\varepsilon^i)^2-\mathbb E\bigl[c(z,f^*(x)+\varepsilon)^2\bigr]\Bigr|\xrightarrow{p}0 .
--   $$
--   4. **Assumption 14** (functional CLT). $g^*_n(\cdot;x)$ and $g(\cdot;x)$ are elements of $C(\mathcal Z)$ and
--   $$
--   \sqrt n\,\bigl(g^*_n(\cdot;x)-g(\cdot;x)\bigr)\xrightarrow{d}V(\cdot;x)\quad\text{in }C(\mathcal Z),
--   $$
--   for some random element $V(\cdot;x)$ of $C(\mathcal Z)$.
--   5. **Assumption 15** (regression rate). For a constant $0<r\le1$,
--   $$
--   \|f^*(x)-\hat f_n(x)\|^2=O_p(n^{-r}),\qquad\frac1n\sum_{i=1}^n\|f^*(x^i)-\hat f_n(x^i)\|^2=O_p(n^{-r}).
--   $$
--
--   Assumption 9 controls how far the sample-robust balls can move the cost; Assumption 12 makes the probability set shrink to the uniform weights; Assumptions 13 and 14 are the full-information SAA's own LLN and CLT; Assumption 15 is the rate of the regression step.
--
--   **Formalization Note** The paper states each assumption "for a.e. $x\in\mathcal X$"; here they are read at the fixed $x$ of the statement. Assumption 12 is printed as an equality for every $n$; at $n=1$ it cannot hold ($\mathfrak P_1\subseteq\{(1)\}$ makes the left side $0$), so it is required for all $n\ge N$, which is all the asymptotic statements use. Suprema over $z$ in Assumption 13 are taken in $[0,\infty]$, the second moments are assumed integrable (Bochner integrals) and bounded above on $\mathcal Z$. Convergence in distribution is Mathlib's `TendstoInDistribution` in the Borel $\sigma$-algebra of $C(\mathcal Z)$ (compact-open topology, which for compact $\mathcal Z$ is the sup-norm topology); it contains the a.e.-measurability of each $\sqrt n(g^*_n-g)$ and of $V$, which lives on its own probability space. $O_p$ is the predicate `IsBigOp`.
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, pp. 21–24, Assumptions 9, 12, 13, 14 and 15

import Mathlib
import Definitions.Def_ResidualsDRO_Unified_IsBigOp
import Definitions.Def_ResidualsDRO_Unified_Setting

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Unified

/-! Assumptions 9, 12, 13, 14 and 15 of Kannan, Bayraksan & Luedtke (2023), §5, pp. 21–24, at a
fixed covariate realization `x` (the paper's "for a.e. x ∈ 𝒳" is read pointwise at `x`). -/

variable {dx dy dz : ℕ} {Ω : Type*}

/-- **Assumption 9** (p. 21): for each `z ∈ 𝒵`, `c(z, ·)` is Lipschitz continuous on `𝒴` with
Lipschitz constant `L(z) ≥ 0`, and `sup_{z ∈ 𝒵} L(z) < +∞`. -/
def Assumption9 (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (𝒴 : Set (EuclideanSpace ℝ (Fin dy))) (𝒵 : Set (EuclideanSpace ℝ (Fin dz)))
    (L : EuclideanSpace ℝ (Fin dz) → ℝ) : Prop :=
  (∀ z ∈ 𝒵, 0 ≤ L z ∧ ∀ y ∈ 𝒴, ∀ y' ∈ 𝒴, |c z y - c z y'| ≤ L z * ‖y - y'‖) ∧
    BddAbove (L '' 𝒵)

/-- **Assumption 12** (p. 21): `sup_{p ∈ 𝔓_n(x; ζ_n(x))} ∑ᵢ (pᵢ - 1/n)² = C_ζ n^{-ρ}` for
constants `ρ > 1` and `C_ζ > 0`, for every sufficiently large `n` (for all `n ≥ N`). The page
states the equality without a threshold; at `n = 1` it is unsatisfiable (`𝔓_1 ⊆ {(1)}` makes the
left side `0`), and for small `n` the right side can exceed the maximum `1 - 1/n` of the left side
over the simplex, so the equality is required eventually. The supremum is a real supremum over
the set `𝔓 n` of probability vectors. -/
def Assumption12 (𝔓 : (n : ℕ) → Set (Fin n → ℝ)) (Cζ ρ : ℝ) : Prop :=
  1 < ρ ∧ 0 < Cζ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n →
    (⨆ p : 𝔓 n, ∑ i, ((p : Fin n → ℝ) i - (n : ℝ)⁻¹) ^ 2) = Cζ * (n : ℝ) ^ (-ρ)

/-- **Assumption 13** (p. 21), weak uniform LLN for the squared cost:
`sup_{z ∈ 𝒵} |(1/n) ∑ᵢ c(z, f*(x) + εⁱ)² - E[c(z, f*(x) + ε)²]| → 0` in probability, with
`sup_{z ∈ 𝒵} E[c(z, f*(x) + ε)²] < +∞` (each second moment finite). The supremum over `z` is
taken in `[0, ∞]`. -/
def Assumption13 [MeasurableSpace Ω] (P : Measure Ω)
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ) (D : ERData dx dy Ω)
    (x : EuclideanSpace ℝ (Fin dx)) (Pε : Measure (EuclideanSpace ℝ (Fin dy)))
    (𝒵 : Set (EuclideanSpace ℝ (Fin dz))) : Prop :=
  (∀ z ∈ 𝒵, Integrable (fun e => (c z (D.fstar x + e)) ^ 2) Pε) ∧
  BddAbove ((fun z => ∫ e, (c z (D.fstar x + e)) ^ 2 ∂Pε) '' 𝒵) ∧
  ∀ η : ℝ, 0 < η → Tendsto (fun n : ℕ => P {ω | ENNReal.ofReal η <
      ⨆ z ∈ 𝒵, ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ i : Fin n, (c z (D.fstar x + D.eps i ω)) ^ 2 -
        ∫ e, (c z (D.fstar x + e)) ^ 2 ∂Pε|}) atTop (𝓝 0)

/-- **Assumption 14** (p. 23), functional CLT for the FI-SAA objective:
`g*_n(·; x)` and `g(·; x)` are elements of `C(𝒵)`, and
`√n (g*_n(·; x) - g(·; x)) → V(·; x)` in distribution in `C(𝒵)` (Borel σ-algebra), where
`V : Ω' → C(𝒵)` is a random element on some probability space `(Ω', P')`. -/
def Assumption14 [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ) (D : ERData dx dy Ω)
    (x : EuclideanSpace ℝ (Fin dx)) (Pε : Measure (EuclideanSpace ℝ (Fin dy)))
    (𝒵 : Set (EuclideanSpace ℝ (Fin dz))) {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (V : Ω' → C(𝒵, ℝ)) : Prop :=
  (∀ n ω, ContinuousOn (gstarN c D x n ω) 𝒵) ∧ ContinuousOn (gTrue c D x Pε) 𝒵 ∧
    TendstoInDistribution (fun n => fcltProcess c D x Pε 𝒵 n) atTop V (fun _ => P) P'

/-- **Assumption 15** (p. 24): a constant `0 < r ≤ 1` with
`‖f*(x) - f̂_n(x)‖² = O_p(n^{-r})` and `(1/n) ∑ᵢ ‖f*(xⁱ) - f̂_n(xⁱ)‖² = O_p(n^{-r})`. -/
def Assumption15 [MeasurableSpace Ω] (P : Measure Ω) (D : ERData dx dy Ω)
    (x : EuclideanSpace ℝ (Fin dx)) (r : ℝ) : Prop :=
  0 < r ∧ r ≤ 1 ∧
  IsBigOp P (fun n ω => ENNReal.ofReal (‖D.fstar x - D.fhat n ω x‖ ^ 2))
    (fun n => (n : ℝ) ^ (-r)) ∧
  IsBigOp P (fun n ω => ENNReal.ofReal ((n : ℝ)⁻¹ *
      ∑ i : Fin n, ‖D.fstar (D.xs i ω) - D.fhat n ω (D.xs i ω)‖ ^ 2))
    (fun n => (n : ℝ) ^ (-r))

end ResidualsDRO.Unified



-- Prove2me | Definitions.Def_QuantumZipper_Welding_Zipper
-- name    : QuantumZipper_Welding_Zipper
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:16:23.447103+00:00
-- url     : https://prove2.me/theorems/cd89f6ab-5367-4cf6-abee-73b81a6cef51
-- title:
--   The capacity zipper law $\Gamma$ (§5.2), restricted to $(h^0,(f_t)_{t\ge0})$; tilted laws; force points of Lemma 5.6
-- statement:
--   This file encodes the law $\Gamma$ of §5.2 through the objects that Proposition 5.4 and Lemma 5.6 use.
--
--   1. **$\Gamma$ on $(h^0,(f_t)_{t\ge0})$.** Under $P$, $B$ is a standard Brownian motion. The zipping-up maps $f_t=g_t-\sqrt\kappa B_t$, $t\ge0$, are the reverse Loewner flow (1.7) on $\mathbb H$ and at every real $x\neq0$ until $f_t(x)$ reaches $0$; they form a reverse $\mathrm{SLE}_\kappa$ flow. The field $h^0$ is normalized by $h^0_1(0)=0$ and has regular arc averages. For every $t\ge0$, given $(B_s)_{s\le t}$, it is Gaussian with the law of $\mathfrak h_t+\tilde h\circ f_t$, where $\tilde h$ is a free boundary GFF: mean $\int\mathfrak h_t\,d\mu$ and covariance $\iint G(f_tu,f_tv)\,\mu(du)\nu(dv)$, both after normalization.
--   2. **Tilt.** $w\cdot P$ normalized to a probability measure, $\big(\int w\,dP\big)^{-1}w\,dP$.
--   3. **Force points of Lemma 5.6.** $\mathcal C_x=\{x\}\cup(\partial B_1(0)\cap\overline{\mathbb H})$, and $\tau_\varepsilon$ is the first time $f_t(\mathcal C_x)$ comes within distance $\varepsilon$ of $0$. With $\varepsilon=0$ this is Theorem 4.5's stopping rule.
--
--   Part 1 is Theorem 1.2 applied at each time $t$, together with the construction of $\Gamma$ (pp. 58–59).
--
--   **Formalization Note** $\Gamma$ is the law of a two-sided stationary process $(h^t,\eta^t)_{t\in\mathbb R}$ built by Kolmogorov consistency. Proposition 5.4 and Lemma 5.6 use only $h^0$ and $f_t$, $t\ge0$. The structure characterizes that restriction, through the joint law of $(h^0,(f_s)_{s\le t})$ for every $t$, and is not the two-sided process. The normalization $h^0_1(0)=0$ is (5.9).
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §5.2, pp. 57–59 (Γ, (5.2)); Proposition 5.4, p. 65; Lemma 5.6, pp. 66–67, (5.9)

import Mathlib
import Definitions.Def_QuantumZipper_Welding_Setting
import Definitions.Def_QuantumZipper_Welding_QuantumLength

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace QuantumZipper.Welding

/-! # The capacity zipper law `Γ` (arXiv:1012.4797v2, §5.2, pp. 57–59), restricted to `t ≥ 0` -/

/-- **The law `Γ`, through `(h⁰, (f_t)_{t ≥ 0})`** (arXiv:1012.4797v2, §5.2, pp. 57–59). Under `P`:
* `B` is a standard Brownian motion and `g` is (almost surely) the reverse Loewner flow (1.7) driven
  by `W_t = √κ B_t`, on `ℍ` and at every real point `x ≠ 0` (until `f_t(x)` hits `0`), so that the
  zipping-up maps `f_t = g_t − W_t`, `t ≥ 0`, are a reverse `SLE_κ` flow (p. 59);
* the field `h⁰` (pairings `Ψ ω μ = (h⁰, μ)`, additive constant fixed by `h⁰₁(0) = 0`) has regular
  arc averages, and for each `t ≥ 0`, conditionally on `(B_s)_{s ≤ t}` (equivalently on `(f_s)_{s ≤ t}`),
  its law is that of `𝔥_t + h̃ ∘ f_t` with `h̃` a free boundary GFF: Gaussian with mean `∫ 𝔥_t dμ` and
  covariance `∫∫ G(f_t(u), f_t(v)) μ(du) ν(dv)` (after the normalization `h₁(0) = 0`). This is
  Theorem 1.2 applied at each `t` together with the construction of `Γ` (pp. 58–59).

**Formalization Note** `Γ` is the law of a two-sided stationary process `(h^t, η^t)_{t ∈ ℝ}` built by
Kolmogorov consistency (p. 58). Propositions 5.4 and Lemma 5.6 use only `h⁰` and the zipping-up maps
`f_t`, `t ≥ 0`; this structure is the characterization of that restriction of `Γ` (the joint law of
`(h⁰, (f_s)_{s ≤ t})` for every `t`), not the two-sided process. The additive constant of `h⁰` is
fixed by `h₁(0) = 0` ((5.9), p. 67), which is what makes `ν_{h⁰}` a measure rather than a measure up
to a constant factor. `g` is required to be measurable in `ω` (it is a.s. a measurable function of
`B`). -/
structure IsGammaZipper {Ω : Type*} [MeasurableSpace Ω] (κ : ℝ) (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (g : Ω → ℝ≥0 → ℂ → ℂ) (Ψ : Ω → Measure ℂ → ℝ) : Prop where
  brownian : IsBrownianReal B P
  flow : ∀ᵐ ω ∂P, QuantumZipper.ReverseCoupling.IsReverseLoewnerFlow (bmDrive κ B ω) (g ω) ∧
    ∀ x : ℝ, x ≠ 0 → IsRealPointFlow (bmDrive κ B ω) (g ω) x
  measurable_flow : ∀ (t : ℝ≥0) (z : ℂ), Measurable fun ω => g ω t z
  regular : ∀ᵐ ω ∂P, IsRegularArcField (Ψ ω)
  law : ∀ t : ℝ≥0, IsCondGaussianFieldOn P (natSigma B t) Set.univ IsAdmissible Ψ
    (fun ω μ => normMean (frakH κ (bmDrive κ B ω) (g ω) t) μ)
    (fun ω μ ν => normCov (revCov (bmDrive κ B ω) (g ω) t) μ ν)

/-- The probability measure `w·P` normalized: the measure whose Radon–Nikodym derivative with
respect to `P` is proportional to `w` ("normalized to be a probability measure", p. 65). -/
noncomputable def tilt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (w : Ω → ℝ≥0∞) :
    Measure Ω :=
  (∫⁻ ω, w ω ∂P)⁻¹ • P.withDensity w

/-- The force-point set `𝒞_x = {x} ∪ (∂B₁(0) ∩ ℍ̄)` of the measure
`ρ_x = γ² δ_x − γ² σ_{0,1}` of Lemma 5.6 (arXiv:1012.4797v2, p. 66). -/
def forceSet (x : ℝ) : Set ℂ :=
  {(x : ℂ)} ∪ {w : ℂ | ‖w‖ = 1 ∧ 0 ≤ w.im}

/-- The first time `f_t(𝒞_x)` comes within distance `ε` of `0`, in `[0, ∞]` (`+∞` if never).
With `ε = 0` this is the stopping rule of Theorem 4.5 (the first time `0 ∈ f_t(𝒞_x)`, p. 52); for
`ε > 0` it is a localizing time strictly before it. -/
noncomputable def hitTime (W : ℝ≥0 → ℝ) (g : ℝ≥0 → ℂ → ℂ) (x : ℝ) (ε : ℝ) : ℝ≥0∞ :=
  sInf {r : ℝ≥0∞ | ∃ s : ℝ≥0, (s : ℝ≥0∞) = r ∧ ∃ y ∈ forceSet x, ‖QuantumZipper.ReverseCoupling.revF W g s y‖ ≤ ε}

end QuantumZipper.Welding



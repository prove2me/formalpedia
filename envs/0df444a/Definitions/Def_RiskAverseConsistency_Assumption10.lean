-- Prove2me | Definitions.Def_RiskAverseConsistency_Assumption10
-- name    : RiskAverseConsistency_Assumption10
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:33.311897+00:00
-- url     : https://prove2.me/theorems/41d4a37e-2b9f-4150-abd5-c86f54389d04
-- title:
--   Assumption 10 (standing hypotheses of Theorem 11)
-- statement:
--   Let $p\in[1,\infty)$, let $(\Omega,\mathcal F,P)$ be a probability space, $\xi:\Omega\to\Xi$ a random element with law $\mathbb P=P\circ\xi^{-1}$, and $F(y)(\omega)=f(y,\xi(\omega))$. **Assumption 10** requires:
--
--   1. $Z$ is a separable, reflexive Banach space and $Z_{\mathrm{ad}}\subset Z$ is nonempty, closed, convex and bounded; $Y$ is a separable Banach space and $Y_0\subset Y$ is closed;
--   2. $\mathbf B:Z\to Y$ is linear and completely continuous, and $\mathbf B(Z_{\mathrm{ad}})\subset Y_0$;
--   3. $\wp:Z\to[0,\infty)$ is convex and continuous;
--   4. $f:Y_0\times\Xi\to\mathbb R$ is a Carathéodory function;
--   5. $f(y,\cdot)\in L^p(\Xi,\mathcal A,\mathbb P)$ for all $y\in Y_0$, and $F:Y_0\to L^p(\Omega,\mathcal F,P)$ is continuous;
--   6. every $\bar y\in Y_0$ has a neighborhood $\mathcal Y_{\bar y}\subset Y_0$ and some $h\in L^p(\Xi,\mathcal A,\mathbb P)$ with $f(y,\cdot)\ge h(\cdot)$ for all $y\in\mathcal Y_{\bar y}$.
--
--   **Formalization Note** $\mathbb P$ is `P.map ξ`; reflexivity is the published `QuasiHemiVI.Existence.IsReflexive`. $f$ is a function on $Y\times\Xi$ of which only values on $Y_0\times\Xi$ matter. Continuity of $F$ is stated sequentially, $\|F(y_k)-F(y)\|_{L^p}\to0$ for $(y_k)\subset Y_0$ with $y_k\to y\in Y_0$, which is equivalent on the metric space $Y_0$. The neighborhood in item 6 is relative to $Y_0$ and the lower bound holds pointwise, as on the page.
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.9, Assumption 10; p.8 ($\mathbb P=P\circ\xi^{-1}$, (9))

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_WeakConv
import Definitions.Def_RiskAverseConsistency_CompletelyContinuousOn
import Definitions.Def_RiskAverseConsistency_IsCaratheodoryOn

open MeasureTheory Filter Topology QuasiHemiVI.Existence

namespace RiskAverseConsistency

/-- **Assumption 10** of Milz–Surowiec, for the data `(p, Z_ad, Y₀, B, ℘, f)` of problem (8) with
`F(y)(ω) := f(y, ξ(ω))`:
1. `Z` is a separable, reflexive Banach space, `Z_ad ⊂ Z` is nonempty, closed, convex and bounded;
   `Y` is a separable Banach space, `Y₀ ⊂ Y` is closed, and `p ∈ [1, ∞)`;
2. `B : Z → Y` is linear and completely continuous and `B(Z_ad) ⊂ Y₀`;
3. `℘ : Z → [0, ∞)` is convex and continuous;
4. `f : Y₀ × Ξ → ℝ` is a Carathéodory function;
5. for all `y ∈ Y₀`, `f(y, ·) ∈ Lᵖ(Ξ, 𝒜, ℙ)`, and `F : Y₀ → Lᵖ(Ω, F, P)` is continuous;
6. for each `ȳ ∈ Y₀` there exist a neighborhood `𝒴_ȳ ⊂ Y₀` of `ȳ` and `h ∈ Lᵖ(Ξ, 𝒜, ℙ)` with
   `f(y, ·) ≥ h(·)` for all `y ∈ 𝒴_ȳ`.

Milz, Surowiec, arXiv:2207.14756v2, Assumption 10, p.9; `ℙ = P ∘ ξ⁻¹` (p.8).

Formalization Note: `ℙ` is `P.map ξ`. Reflexivity is the published `QuasiHemiVI.Existence.IsReflexive`
(the canonical map into the bidual is onto). `B` is a linear map; complete continuity is
`CompletelyContinuousOn univ`. `f` is a function on `Y × Ξ` of which only the values on `Y₀ × Ξ`
matter. Continuity of `F : Y₀ → Lᵖ(Ω)` is stated sequentially, as `‖F(yₖ) − F(y)‖_{Lᵖ} → 0` for
`(yₖ) ⊂ Y₀`, `yₖ → y ∈ Y₀` (equivalent, since `Y₀` is a metric space). "Neighborhood of `ȳ` in `Y₀`"
is a neighborhood in the relative topology (`𝓝[Y₀] ȳ`); the lower bound holds pointwise, as on the
page. -/
structure Assumption10 {Ω Ξ Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (p : ENNReal) (P : Measure Ω) (ξ : Ω → Ξ) (Zad : Set Z) (Y₀ : Set Y) (B : Z →ₗ[ℝ] Y)
    (φ : Z → ℝ) (f : Y → Ξ → ℝ) : Prop where
  Z_complete : CompleteSpace Z
  Z_separable : TopologicalSpace.SeparableSpace Z
  Z_reflexive : IsReflexive Z
  Zad_nonempty : Zad.Nonempty
  Zad_closed : IsClosed Zad
  Zad_convex : Convex ℝ Zad
  Zad_bounded : Bornology.IsBounded Zad
  Y_complete : CompleteSpace Y
  Y_separable : TopologicalSpace.SeparableSpace Y
  Y₀_closed : IsClosed Y₀
  one_le_p : 1 ≤ p
  p_ne_top : p ≠ ⊤
  B_completelyContinuous : CompletelyContinuousOn Set.univ B
  B_mapsTo : Set.MapsTo B Zad Y₀
  φ_nonneg : ∀ z, 0 ≤ φ z
  φ_convex : ConvexOn ℝ Set.univ φ
  φ_continuous : Continuous φ
  f_caratheodory : IsCaratheodoryOn Y₀ f
  f_memLp : ∀ y ∈ Y₀, MemLp (f y) p (P.map ξ)
  F_continuous : ∀ y ∈ Y₀, ∀ u : ℕ → Y, (∀ k, u k ∈ Y₀) → Tendsto u atTop (𝓝 y) →
    Tendsto (fun k => eLpNorm (fun ω => f (u k) (ξ ω) - f y (ξ ω)) p P) atTop (𝓝 0)
  f_lowerBound : ∀ y₁ ∈ Y₀, ∃ 𝒴 : Set Y, 𝒴 ⊆ Y₀ ∧ 𝒴 ∈ 𝓝[Y₀] y₁ ∧
    ∃ h : Ξ → ℝ, MemLp h p (P.map ξ) ∧ ∀ y ∈ 𝒴, ∀ x : Ξ, h x ≤ f y x

end RiskAverseConsistency



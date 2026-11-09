-- Prove2me | Definitions.Def_MatchingGFT_TightE_Quantile
-- name    : MatchingGFT_TightE_Quantile
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:14.210827+00:00
-- url     : https://prove2.me/theorems/c37bcca8-d74d-476f-badb-09c8d9192150
-- title:
--   Quantiles, revenue and cost curves, ironing, virtual functions
-- statement:
--   The upper quantile $Q_i(\rho)=\sup\{x:P(v\ge x)\ge\rho\}$ and lower quantile $Q_j(\sigma)=\inf\{x:P(c\le x)\ge\sigma\}$; the curves $R(\rho)=\rho Q(\rho)$, $K(\sigma)=\sigma Q(\sigma)$ with value $0$ at $0$ and left limits at $1$ ($K(1)=+\infty$ allowed); the smallest concave majorant of $R$ and the largest convex minorant of $K$; their left derivatives $\Phi,\Psi$ on $(0,1)$; and $\phi(v)=\sup\{\Phi(\rho):\rho\in(0,1),Q(\rho)\le v\}$, $\psi(c)=\inf\{\Psi(\sigma):\sigma\in(0,1),Q(\sigma)\ge c\}$ in the extended reals with $\sup\emptyset=-\infty$, $\inf\emptyset=+\infty$.
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), §2.1–2.2, Appendix A, PDF pp. 9–10, 24

import Mathlib

open MeasureTheory Set

namespace MatchingGFT.TightE

/-- The buyer upper-quantile function of a law `F` (PDF pp. 9, 24):
`Q(ρ) = sup {x : P(v ≥ x) ≥ ρ}`. For `ρ ∈ (0, 1)` and a nonnegative law this is the nonincreasing
left-continuous version with `Q(U) ∼ F`. -/
noncomputable def buyerQuantile (F : Measure ℝ) (ρ : ℝ) : ℝ :=
  sSup {x : ℝ | ρ ≤ F.real (Ici x)}

/-- The seller lower-quantile function of a law `G` (PDF pp. 9, 24):
`Q(σ) = inf {x : P(c ≤ x) ≥ σ}`, nondecreasing and left-continuous on `(0, 1)` with `Q(U) ∼ G`. -/
noncomputable def sellerQuantile (G : Measure ℝ) (σ : ℝ) : ℝ :=
  sInf {x : ℝ | σ ≤ G.real (Iic x)}

/-- The revenue curve on `[0, 1]` (PDF p. 9): `R(0) = 0`, `R(ρ) = ρ Q(ρ)`, and `R(1)` is the left
limit at `1`. -/
noncomputable def revCurve (F : Measure ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0
  else if x = 1 then Function.leftLim (fun ρ : ℝ => ρ * buyerQuantile F ρ) 1
  else x * buyerQuantile F x

/-- The procurement-cost curve on `[0, 1]` (PDF p. 9): `K(0) = 0`, `K(σ) = σ Q(σ)`, and `K(1)` is the
left limit at `1`, which may be `+∞`. -/
noncomputable def costCurve (G : Measure ℝ) (x : ℝ) : EReal :=
  if x = 0 then 0
  else if x = 1 then Function.leftLim (fun σ : ℝ => ((σ * sellerQuantile G σ : ℝ) : EReal)) 1
  else ((x * sellerQuantile G x : ℝ) : EReal)

/-- The pointwise smallest concave function above `R` on `[0, 1]` (PDF p. 10). -/
noncomputable def revHull (F : Measure ℝ) (x : ℝ) : ℝ :=
  sInf {y : ℝ | ∃ g : ℝ → ℝ, ConcaveOn ℝ (Icc 0 1) g ∧
    (∀ z ∈ Icc (0 : ℝ) 1, revCurve F z ≤ g z) ∧ y = g x}

/-- The pointwise largest convex function below `K` on `[0, 1]` (PDF p. 10), at points of `[0, 1)`.
The curve `K` is compared in `EReal`, so `K(1) = +∞` imposes nothing at `1`; the supremum over
finite convex minorants is the value of the extended convex minorant at every `x < 1`. -/
noncomputable def costHull (G : Measure ℝ) (x : ℝ) : ℝ :=
  sSup {y : ℝ | ∃ g : ℝ → ℝ, ConvexOn ℝ (Icc 0 1) g ∧
    (∀ z ∈ Icc (0 : ℝ) 1, ((g z : ℝ) : EReal) ≤ costCurve G z) ∧ y = g x}

/-- `Φ(ρ)`: the left derivative of the concave majorant at `ρ ∈ (0, 1)` (PDF p. 10). -/
noncomputable def ironedSlopeBuyer (F : Measure ℝ) (ρ : ℝ) : ℝ :=
  derivWithin (revHull F) (Iio ρ) ρ

/-- `Ψ(σ)`: the left derivative of the convex minorant at `σ ∈ (0, 1)` (PDF p. 10). -/
noncomputable def ironedSlopeSeller (G : Measure ℝ) (σ : ℝ) : ℝ :=
  derivWithin (costHull G) (Iio σ) σ

/-- The type-space ironed virtual value (PDF p. 10):
`φ(v) = sup {Φ(ρ) : ρ ∈ (0, 1), Q(ρ) ≤ v}` with `sup ∅ = -∞`. -/
noncomputable def virtualValue (F : Measure ℝ) (v : ℝ) : EReal :=
  sSup ((fun ρ : ℝ => ((ironedSlopeBuyer F ρ : ℝ) : EReal)) ''
    {ρ : ℝ | ρ ∈ Ioo (0 : ℝ) 1 ∧ buyerQuantile F ρ ≤ v})

/-- The type-space ironed virtual cost (PDF p. 10):
`ψ(c) = inf {Ψ(σ) : σ ∈ (0, 1), Q(σ) ≥ c}` with `inf ∅ = +∞`. -/
noncomputable def virtualCost (G : Measure ℝ) (c : ℝ) : EReal :=
  sInf ((fun σ : ℝ => ((ironedSlopeSeller G σ : ℝ) : EReal)) ''
    {σ : ℝ | σ ∈ Ioo (0 : ℝ) 1 ∧ c ≤ sellerQuantile G σ})

end MatchingGFT.TightE



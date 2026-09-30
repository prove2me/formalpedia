-- Prove2me | Definitions.Def_StarShapedRisk_Representation_RiskMeasure
-- name    : StarShapedRisk_Representation_RiskMeasure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:43:28.827809+00:00
-- url     : https://prove2.me/theorems/abcc18b0-2416-4fe4-b65c-f4998f7fec37
-- title:
--   Definition 1 — risk measures on a space of bounded positions: monotone, translation invariant, normalized; star-shaped, convex, coherent
-- statement:
--   Let $\Omega$ be a set of states of the environment. A **space of positions** $\mathcal X$ is a linear space of real functions on $\Omega$ such that
--
--   1. every $X\in\mathcal X$ is bounded, and
--   2. $\mathcal X$ contains every constant function; the constant $m\in\mathbb R$ is identified with the constant position $m$.
--
--   No probability measure is fixed on $\Omega$. A value $X(\omega)>0$ is a **loss**. $\mathcal X$ carries the pointwise order: $X\geqq Y$ if and only if $X(\omega)\ge Y(\omega)$ for every $\omega$.
--
--   A **risk measure** is a function $\rho:\mathcal X\to\mathbb R$ satisfying
--
--   1. *monotonicity*: $X\geqq Y$ implies $\rho(X)\ge\rho(Y)$;
--   2. *translation invariance*: $\rho(X-m)=\rho(X)-m$ for all $X\in\mathcal X$ and $m\in\mathbb R$;
--   3. *normalization*: $\rho(0)=0$.
--
--   A risk measure may have the further properties
--
--   4. *star-shapedness*: $\rho(\lambda X)\ge\lambda\rho(X)$ for all $X$ and all $\lambda>1$;
--   5. *convexity*: $\rho(\lambda X+(1-\lambda)Y)\le\lambda\rho(X)+(1-\lambda)\rho(Y)$ for all $X,Y$ and all $\lambda\in(0,1)$;
--   6. *positive homogeneity*: $\rho(\lambda X)=\lambda\rho(X)$ for all $X$ and all $\lambda>0$;
--   7. *subadditivity*: $\rho(X+Y)\le\rho(X)+\rho(Y)$ for all $X,Y$.
--
--   A **star-shaped** (resp. **convex**) risk measure is a risk measure with property 4 (resp. 5); a **coherent** risk measure is a risk measure with properties 6 and 7.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** The space of positions is a structure `PositionSpace Ω` bundling a `Submodule ℝ (Ω → ℝ)` with the constants and boundedness conditions; positions are elements of the subtype `𝒳.carrier`, and `𝒳.const m` is the constant position $m$. Each property is its own predicate (`IsMonotone`, …, `IsSubadditive`), and `IsRiskMeasure`, `IsStarShapedRiskMeasure`, `IsConvexRiskMeasure`, `IsCoherentRiskMeasure` bundle them. Monotonicity is written with the pointwise order.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2641, Section 3 (standing assumptions on 𝒳) and Definition 1

import Mathlib

namespace StarShapedRisk.Representation

/-- The space of positions of Castagnoli et al. (2022), Sec. 3: a linear space `carrier` of
bounded real functions on the state space `Ω` that contains every constant function. No
probability measure is fixed and measurability plays no role. A value `X ω > 0` is a loss. -/
structure PositionSpace (Ω : Type*) where
  /-- The linear space `𝒳` of positions. -/
  carrier : Submodule ℝ (Ω → ℝ)
  /-- `𝒳` contains all constants. -/
  const_mem : ∀ c : ℝ, (fun _ : Ω => c) ∈ carrier
  /-- Every position is a bounded function. -/
  bounded : ∀ X ∈ carrier, ∃ C : ℝ, ∀ ω, |X ω| ≤ C

variable {Ω : Type*}

/-- The constant position `m`. -/
def PositionSpace.const (𝒳 : PositionSpace Ω) (m : ℝ) : 𝒳.carrier :=
  ⟨fun _ => m, 𝒳.const_mem m⟩

/-- Definition 1.1, monotonicity: if `X ≧ Y` pointwise, then `ρ X ≥ ρ Y`. -/
def IsMonotone (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ) : Prop :=
  ∀ X Y : 𝒳.carrier, (∀ ω, Y.1 ω ≤ X.1 ω) → ρ Y ≤ ρ X

/-- Definition 1.2, translation invariance: `ρ (X - m) = ρ X - m` for all `X` and real `m`. -/
def IsTranslationInvariant (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ) : Prop :=
  ∀ (X : 𝒳.carrier) (m : ℝ), ρ (X - 𝒳.const m) = ρ X - m

/-- Definition 1.3, normalization: `ρ 0 = 0`. -/
def IsNormalized (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ) : Prop :=
  ρ 0 = 0

/-- Definition 1: a risk measure is monotone, translation invariant and normalized. -/
def IsRiskMeasure (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ) : Prop :=
  IsMonotone 𝒳 ρ ∧ IsTranslationInvariant 𝒳 ρ ∧ IsNormalized 𝒳 ρ

/-- Definition 1.4, star-shapedness: `ρ (t X) ≥ t ρ X` for all `X` and all `t > 1`. -/
def IsStarShaped (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ) : Prop :=
  ∀ (X : 𝒳.carrier) (t : ℝ), 1 < t → t * ρ X ≤ ρ (t • X)

/-- Definition 1.5, convexity: `ρ (t X + (1 - t) Y) ≤ t ρ X + (1 - t) ρ Y` for `t ∈ (0,1)`. -/
def IsConvex (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ) : Prop :=
  ∀ (X Y : 𝒳.carrier) (t : ℝ), 0 < t → t < 1 →
    ρ (t • X + (1 - t) • Y) ≤ t * ρ X + (1 - t) * ρ Y

/-- Definition 1.6, positive homogeneity: `ρ (t X) = t ρ X` for all `X` and all `t > 0`. -/
def IsPositivelyHomogeneous (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ) : Prop :=
  ∀ (X : 𝒳.carrier) (t : ℝ), 0 < t → ρ (t • X) = t * ρ X

/-- Definition 1.7, subadditivity: `ρ (X + Y) ≤ ρ X + ρ Y`. -/
def IsSubadditive (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ) : Prop :=
  ∀ X Y : 𝒳.carrier, ρ (X + Y) ≤ ρ X + ρ Y

/-- A star-shaped risk measure: a risk measure satisfying Definition 1.4. -/
def IsStarShapedRiskMeasure (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ) : Prop :=
  IsRiskMeasure 𝒳 ρ ∧ IsStarShaped 𝒳 ρ

/-- A convex risk measure: a risk measure satisfying Definition 1.5. -/
def IsConvexRiskMeasure (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ) : Prop :=
  IsRiskMeasure 𝒳 ρ ∧ IsConvex 𝒳 ρ

/-- A coherent risk measure: a positively homogeneous and subadditive risk measure. -/
def IsCoherentRiskMeasure (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ) : Prop :=
  IsRiskMeasure 𝒳 ρ ∧ IsPositivelyHomogeneous 𝒳 ρ ∧ IsSubadditive 𝒳 ρ

end StarShapedRisk.Representation



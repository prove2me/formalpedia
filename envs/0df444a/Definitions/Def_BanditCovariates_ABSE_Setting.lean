-- Prove2me | Definitions.Def_BanditCovariates_ABSE_Setting
-- name    : BanditCovariates_ABSE_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:06:03.177983+00:00
-- url     : https://prove2.me/theorems/e63185d0-9bc2-4e75-bb30-b3bc68d77fd3
-- title:
--   §§2–3 — machine, covariate means, class, and confidence radius
-- statement:
--   A $K$-armed covariate bandit machine consists of independent vectors $(X_t,Y_t^{(1)},\ldots,Y_t^{(K)})$ over time. The covariates have common law $P_X$ on the Euclidean unit cube $\mathcal X=[0,1]^d$. Rewards are in $[0,1]$, with conditional arm means $f^{(i)}(X_t)\in[0,1]$; the reward vectors need not be identically distributed. Write $f^*(x)=\max_i f^{(i)}(x)$ and $f^\sharp(x)$ for the largest strictly smaller arm mean, or $f^*(x)$ if all means tie.
--
--   The class $\mathcal M^K_{\mathcal X}(\alpha,\beta,L)$ has Euclidean $(\beta,L)$-Hölder arm means, a covariate density between $0<\underline c\le\overline c$, and the margin condition
--
--   $$P_X\{0<f^*(X)-f^\sharp(X)\le\delta\}\le C_0\delta^\alpha\qquad(0\le\delta\le\delta_0).$$
--
--   The file also defines $\overline{\log}(x)=\max\{\log x,1\}$ and $U(s,T)=2\sqrt{2\overline{\log}(T/s)/s}$. These definitions fix the model used by the regret theorem.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, pp. 5, 10–13, (2.1), §3.1–3.2

import Mathlib
import Definitions.Def_BanditCovariates_SE_Setting

noncomputable section

namespace BanditCovariates.ABSE

open MeasureTheory ProbabilityTheory

abbrev Covariate (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The unit cube in Euclidean space; dimension zero is excluded in the results. -/
def cube (d : ℕ) : Set (Covariate d) :=
  {x | ∀ j : Fin d, x j ∈ Set.Icc (0 : ℝ) 1}

/-- The stochastic data of a covariate bandit. Time starts at zero in Lean. -/
structure Machine (d K : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  PX : Measure (Covariate d)
  X : ℕ → Ω → Covariate d
  Y : ℕ → Ω → Fin K → ℝ
  f : Fin K → Covariate d → ℝ

/-- The assumptions of §3.1, including the conditional mean identity expressed on
all covariate events. Rewards at different times need not have the same law. -/
def IsMachine {d K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Machine d K Ω) : Prop :=
  IsProbabilityMeasure M.P ∧ IsProbabilityMeasure M.PX ∧
  (∀ t, Measurable (M.X t)) ∧
  (∀ t i, Measurable (fun ω => M.Y t ω i)) ∧
  (∀ i, Measurable (M.f i)) ∧
  iIndepFun (fun t ω => (M.X t ω, M.Y t ω)) M.P ∧
  (∀ t, Measure.map (M.X t) M.P = M.PX) ∧
  M.PX (cube d)ᶜ = 0 ∧
  (∀ t ω i, M.Y t ω i ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ i x, x ∈ cube d → M.f i x ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ t i A, MeasurableSet A →
    (∫ ω in (M.X t) ⁻¹' A, M.Y t ω i ∂M.P) =
      ∫ ω in (M.X t) ⁻¹' A, M.f i (M.X t ω) ∂M.P)

/-- A finite maximum, initialized at zero. On the cube, all means lie in [0,1]. -/
def fStar {d K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Machine d K Ω) (x : Covariate d) : ℝ :=
  (Finset.univ.toList.map (fun i : Fin K => M.f i x)).foldl max 0

/-- The largest arm mean strictly below the maximum, or the maximum itself
when all arm means tie. -/
def fSharp {d K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Machine d K Ω) (x : Covariate d) : ℝ :=
  let S := Finset.univ.filter (fun i : Fin K => M.f i x < fStar M x)
  if S.Nonempty then (S.toList.map (fun i => M.f i x)).foldl max 0
  else fStar M x

/-- A density between `cLow` and `cHigh` relative to Lebesgue measure. -/
def HasDensityBounds {d K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Machine d K Ω) (cLow cHigh : ℝ) : Prop :=
  ∀ A : Set (Covariate d), MeasurableSet A → A ⊆ cube d →
    ENNReal.ofReal cLow * volume A ≤ M.PX A ∧
    M.PX A ≤ ENNReal.ofReal cHigh * volume A

/-- The Euclidean Hölder condition of §3.2. -/
def IsHolder {d K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Machine d K Ω) (β L : ℝ) : Prop :=
  ∀ i x, x ∈ cube d → ∀ y, y ∈ cube d →
    |M.f i x - M.f i y| ≤ L * ‖x - y‖ ^ β

/-- The paper's strict-gap margin condition. -/
def HasMargin {d K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Machine d K Ω) (α δ₀ C₀ : ℝ) : Prop :=
  ∀ δ ∈ Set.Icc (0 : ℝ) δ₀,
    (M.PX {x | 0 < fStar M x - fSharp M x ∧
                 fStar M x - fSharp M x ≤ δ}).toReal ≤ C₀ * δ ^ α

/-- The class `𝓜^K_𝒳(α,β,L)` with explicit margin and density constants. -/
def InClass {d K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Machine d K Ω) (β L α δ₀ C₀ cLow cHigh : ℝ) : Prop :=
  IsMachine M ∧ HasDensityBounds M cLow cHigh ∧
  IsHolder M β L ∧ HasMargin M α δ₀ C₀

def U (s : ℕ) (T : ℝ) : ℝ :=
  2 * Real.sqrt (2 * BanditCovariates.SE.logbar (T / (s : ℝ)) / (s : ℝ))

end BanditCovariates.ABSE



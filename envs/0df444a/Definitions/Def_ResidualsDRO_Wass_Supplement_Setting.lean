-- Prove2me | Definitions.Def_ResidualsDRO_Wass_Supplement_Setting
-- name    : ResidualsDRO_Wass_Supplement_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:33:30.819102+00:00
-- url     : https://prove2.me/theorems/444110d2-8335-4672-8bc2-823e9a1d8b1d
-- title:
--   §2–3, §5 — sequence model, true and robust optimization, convergence and Lq norms
-- statement:
--   Let X, Y and z range over finite-dimensional Euclidean spaces, with probability laws P_X and P_ε, covariate range 𝒳, response range 𝒴, decision set 𝒵, and cost c. The data are the published sequence of regression estimates and observations. The conditional law is the law of f*(x)+ε. The definitions add the sequence-level optimization and convergence interfaces:
--
--   $$g(z;x)=E[c(z,f^*(x)+\varepsilon)],\quad v^*(x)=\min_{z\in\mathcal Z}g(z;x),\quad S^*(x)=\arg\min_{z\in\mathcal Z}g(z;x).$$
--
--   Wasserstein objectives, empirical laws and radius formulas reuse published definitions. The unified objective also reuses the published model; its value and entire optimizer set are constructed, not free parameters. The definitions include convergence in probability, one-sided set deviation, and the full Lq(P_X) norm for 1≤q≤∞. Positive sample sizes use Fin n. Standing conditions spell out compactness, cost integrability, projection, and the real-valued lower semicontinuous robust objective; extended norms preserve infinite values. This layer allows every new theorem to share the same optimization objects.
--
--   Differences from the source:
--
--   - generalization: the observations follow the joint covariate/error model and the regression estimate is constructed from the first n observations → the reduced interface retains support, the conditional response law and the displayed statistical assumptions, without requiring a joint training-covariate law, covariate/error independence or dependence of the estimator only on the first n observations; reason: the estimates below use only the explicit statistical predicates and pathwise residual/projection identities; every source data model supplies this interface, so no source instance is excluded
--   - encoding: minima, probability convergence, Lq norms and one-sided set deviation on the source domains → constructed infima and optimizer sets with compact nonempty lsc optimization guards; nonnegative extended errors and full q=∞ norms; reason: these agree on the theorem domains and keep unbounded errors infinite instead of replacing them by a real supremum default
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Mathematical Programming (2023), accepted manuscript, https://doi.org/10.1007/s10107-023-02014-7, pp. 6–11, 20–21

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Radius
import Definitions.Def_ResidualsDRO_Unified_Assumptions

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Wass.Supplement

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Additional data, not additional restrictions: the published ERData, the covariate
law and range, error law, compact decision set and cost. Sections 2.1–2.2, pp. 6–9. -/
structure Model (dx dy dz : ℕ) (Ω : Type*) where
  D : Unified.ERData dx dy Ω
  PX : Measure (E dx)
  X : Set (E dx)
  Pε : Measure (E dy)
  Z : Set (E dz)
  c : E dz → E dy → ℝ

variable {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω]

noncomputable def g (M : Model dx dy dz Ω) (x : E dx) (z : E dz) : ℝ :=
  trueObjective M.Pε M.D.fstar M.c x z

noncomputable def vstar (M : Model dx dy dz Ω) (x : E dx) : ℝ := sInf (g M x '' M.Z)

def solutions (M : Model dx dy dz Ω) (x : E dx) : Set (E dz) :=
  {z | z ∈ M.Z ∧ ∀ u ∈ M.Z, g M x z ≤ g M x u}

noncomputable def PER (M : Model dx dy dz Ω) (x : E dx) (n : ℕ) (ω : Ω) : Measure (E dy) :=
  erEmpirical (n := n) M.D.proj M.D.fstar (M.D.fhat n ω) (fun i => M.D.xs i ω)
    (fun i => M.D.eps i ω) x

noncomputable def Pstar (M : Model dx dy dz Ω) (x : E dx) (n : ℕ) (ω : Ω) : Measure (E dy) :=
  trueEmpirical (n := n) M.D.fstar (fun i => M.D.eps i ω) x

noncomputable def law (M : Model dx dy dz Ω) (x : E dx) : Measure (E dy) :=
  condLaw M.Pε M.D.fstar x

/-- Standing assumptions on pp. 6–9, at a covariate where they hold. No i.i.d.
restriction is put here: the unified results admit dependent observations. -/
def Standing (M : Model dx dy dz Ω) (P : Measure Ω) (x : E dx) : Prop :=
  x ∈ M.X ∧ IsProbabilityMeasure P ∧ IsProbabilityMeasure M.Pε ∧
  IsProbabilityMeasure M.PX ∧ M.PX M.Xᶜ = 0 ∧
  M.Z.Nonempty ∧ IsCompact M.Z ∧ M.D.𝒴.Nonempty ∧ IsClosed M.D.𝒴 ∧
  Convex ℝ M.D.𝒴 ∧ IsNearestPointProj M.D.𝒴 M.D.proj ∧
  Measurable M.D.proj ∧ Measurable M.D.fstar ∧ Integrable id M.Pε ∧ (∫ e, e ∂M.Pε) = 0 ∧
  (∀ᵐ e ∂M.Pε, M.D.fstar x + e ∈ M.D.𝒴) ∧
  (∀ n, ∀ᵐ ω ∂P, M.D.xs n ω ∈ M.X ∧ M.D.fstar x + M.D.eps n ω ∈ M.D.𝒴) ∧
  (∀ z ∈ M.Z, Integrable (fun e => M.c z (M.D.fstar x + e)) M.Pε) ∧
  LowerSemicontinuousOn (g M x) M.Z

def IID (M : Model dx dy dz Ω) (P : Measure Ω) : Prop :=
  ProbabilityTheory.iIndepFun M.D.eps P ∧
  ∀ i, Measurable (M.D.eps i) ∧ Measure.map (M.D.eps i) P = M.Pε

noncomputable def wobj (M : Model dx dy dz Ω) (x : E dx) (p ζ : ℝ)
    (n : ℕ) (ω : Ω) (z : E dz) : EReal :=
  WassersteinDRO.Duality.worstCaseRisk ζ p M.D.𝒴 (PER M x n ω) (M.c z)

noncomputable def wvalue (M : Model dx dy dz Ω) (x : E dx) (p ζ : ℝ)
    (n : ℕ) (ω : Ω) : ℝ := (erDROValue M.Z M.c ζ p M.D.𝒴 (PER M x n ω)).toReal

/-- The objective of (8) is real valued and lsc, p. 9. These conditions ensure
that the EReal-to-real conversion above never replaces infinity by zero. -/
def WRegular (M : Model dx dy dz Ω) (x : E dx) (p ζ : ℝ) (n : ℕ) : Prop :=
  ∀ ω, (∀ z ∈ M.Z, ∃ t : ℝ, wobj M x p ζ n ω z = (t : EReal)) ∧
    LowerSemicontinuousOn (fun z => (wobj M x p ζ n ω z).toReal) M.Z

def WSelect (M : Model dx dy dz Ω) (x : E dx) (p : ℝ) (ζ : ℕ → ℝ)
    (zhat : ℕ → Ω → E dz) : Prop :=
  ∀ n, 1 ≤ n → ∀ ω, zhat n ω ∈ M.Z ∧
    wobj M x p (ζ n) n ω (zhat n ω) = (wvalue M x p (ζ n) n ω : EReal)

/-- Convergence in probability, with outer probabilities, including infinite errors. -/
def Vanishes (P : Measure Ω) (V : ℕ → Ω → ℝ≥0∞) : Prop :=
  ∀ η : ℝ, 0 < η → Tendsto (fun n => P {ω | ENNReal.ofReal η < V n ω}) atTop (𝓝 0)

noncomputable def error (a b : ℝ) : ℝ≥0∞ := ENNReal.ofReal |a - b|

/-- The full L^q(P_X) norm, including q = ∞ (ess sup), with data held fixed. -/
noncomputable def lq (M : Model dx dy dz Ω) (q : ℝ≥0∞) (F : E dx → ℝ) : ℝ≥0∞ :=
  eLpNorm F q M.PX

noncomputable def uobj (M : Model dx dy dz Ω)
    (ps : E dx → (n : ℕ) → Set (Fin n → ℝ)) (μ : E dx → ℕ → ℝ)
    (x : E dx) (n : ℕ) (ω : Ω) (z : E dz) : ℝ :=
  Unified.ghatER M.c M.D x (ps x) (μ x) n ω z

noncomputable def uvalue (M : Model dx dy dz Ω)
    (ps : E dx → (n : ℕ) → Set (Fin n → ℝ)) (μ : E dx → ℕ → ℝ)
    (x : E dx) (n : ℕ) (ω : Ω) : ℝ := sInf (uobj M ps μ x n ω '' M.Z)

def usolutions (M : Model dx dy dz Ω)
    (ps : E dx → (n : ℕ) → Set (Fin n → ℝ)) (μ : E dx → ℕ → ℝ)
    (x : E dx) (n : ℕ) (ω : Ω) : Set (E dz) :=
  {z | z ∈ M.Z ∧ ∀ u ∈ M.Z, uobj M ps μ x n ω z ≤ uobj M ps μ x n ω u}

/-- Probability simplex condition (9), positive sample sizes, and the standing
real-valued/lsc condition of p. 9. The inner suprema are bounded because the
scenario balls are compact and the cost is Lipschitz in every theorem using them. -/
def URegular (M : Model dx dy dz Ω)
    (ps : E dx → (n : ℕ) → Set (Fin n → ℝ)) (μ : E dx → ℕ → ℝ) (x : E dx) : Prop :=
  ∀ n, 1 ≤ n → 0 ≤ μ x n ∧ (ps x n).Nonempty ∧
    (∀ p ∈ ps x n, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) ∧
    ∀ ω, LowerSemicontinuousOn (uobj M ps μ x n ω) M.Z ∧
      ∀ z ∈ M.Z, ∀ i : Fin n,
        BddAbove (M.c z '' Unified.scenarioBall M.D x (μ x n) n ω i)

noncomputable def deviation (A B : Set (E dz)) : ℝ≥0∞ :=
  ⨆ z ∈ A, (⨅ w ∈ B, edist z w)

noncomputable def uniformError (M : Model dx dy dz Ω)
    (F : E dz → ℝ) (x : E dx) : ℝ≥0∞ := ⨆ z ∈ M.Z, error (F z) (g M x z)

end ResidualsDRO.Wass.Supplement



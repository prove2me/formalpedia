-- Prove2me | Definitions.Def_DistTransform_Distortion_Supplement_RiskModel
-- name    : DistTransform_Distortion_Supplement_RiskModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T13:08:16.357227+00:00
-- url     : https://prove2.me/theorems/67670bd5-cd40-4a49-b189-73ff56e9a8b2
-- title:
--   §5 — law-invariant inputs, distributional evaluation, generated risks, VaR and ES
-- statement:
--   Fix an arbitrary atomless probability space (Ω,𝓕,P). The domain L∞ consists of measurable real losses that are bounded almost surely. The published risk classes retain Definition 4: monetary means monotone for almost-sure order and cash invariant; convex risk means monetary and convex; coherent means convex risk and positively homogeneous. Convex mixtures include λ=0 and λ=1, and positive homogeneity uses every λ>0. No normalization or Fatou property is imposed.
--
--   For a law-invariant input ρ, the distributional functional and the generated risk are
--
--   $$
--   \widehat\rho(F)=\rho(X)\quad(X\sim F),\qquad \rho_T(X)=\widehat\rho(T(F_X)).
--   $$
--
--   The input type carries law invariance. The structural lemma rhoHat_eq proves independence from every measurable essentially bounded representative with the given law. On an atomless probability space every bounded law has such a representative. The actual law F_X is a measurable pushforward.
--
--   For p∈(0,1), the distributional Value-at-Risk and Expected Shortfall are
--
--   $$
--   \mathrm{VaR}_p(F)=F^{-1}(p),\qquad \mathrm{ES}_p(F)=\frac1{1-p}\int_p^1 F^{-1}(t)\,dt.
--   $$
--
--   The generated ES is evaluated directly as ES_p(T(F_X)), giving the same law-invariant construction without choosing a representative of the ES functional. These objects connect bounded-law transforms with ordinary convex and coherent risk classes.
--
--   **Formalization Note** Raw functions represent L∞ classes; the reused axioms use almost-sure order, so monetary risks descend to equality almost surely. The reused cash axiom ρ(X−m)=ρ(X)−m is exactly ρ(X+c)=ρ(X)+c after m=−c. The fallback values of rhoHat for a non-realizable law, and of law for a nonmeasurable input, are never used on the stated atomless bounded domain. The ES integral uses the open interval (p,1), omitting only null endpoints so no totalized endpoint quantile is evaluated.
-- source:
--   Liu, Schied and Wang, Distributional transforms, probability distortions, and their applications, SSRN 3419388 (version of March 19, 2020), pp. 15–16, Definition 4, distributional risk generation, VaR and ES; §2, p. 3, atomless setting

import Mathlib
import Definitions.Def_DistTransform_Distortion_Supplement_Algebra
import Definitions.Def_TailRiskTheory_Generator_Model

namespace DistTransform.Distortion.Supplement

open MeasureTheory ProbabilityTheory
open TailRiskSharing.TailConv (Linf)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- p. 16: risks allowed as inputs to the law-based construction. The published
law-invariance predicate equates cdfs; there is no convexity, normalization or Fatou axiom here. -/
def LawInvariantRisk (P : Measure Ω) :=
  {ρ : (Ω → ℝ) → ℝ // TailRiskSharing.VaRTail.IsLawInvariant P (Linf P) ρ}

/-- A random variable has law F, expressed through the source's cdf identification. -/
def HasLaw (P : Measure Ω) (X : Ω → ℝ) (F : ProbabilityMeasure ℝ) : Prop :=
  ∀ x : ℝ, TailRiskSharing.VaRConv.distFn P X x = cdf (F : Measure ℝ) x

/-- p. 16: evaluate a law-invariant input on any L∞ representative of F.
The fallback is outside the intended domain: every bounded law has a representative
on every atomless probability space. Independence is proved below. -/
noncomputable def rhoHat (P : Measure Ω) (ρ : LawInvariantRisk P)
    (F : ProbabilityMeasure ℝ) : ℝ := by
  classical
  exact if h : ∃ X : Ω → ℝ, X ∈ Linf P ∧ HasLaw P X F then ρ.val h.choose else 0

/-- Structural well-definedness: every admissible representative gives exactly the same value.
This uses only the law-invariance field, not a risk-measure theorem. -/
theorem rhoHat_eq (P : Measure Ω) (ρ : LawInvariantRisk P)
    (F : ProbabilityMeasure ℝ) (X : Ω → ℝ) (hX : X ∈ Linf P) (hF : HasLaw P X F) :
    rhoHat P ρ F = ρ.val X := by
  classical
  have hex : ∃ Y : Ω → ℝ, Y ∈ Linf P ∧ HasLaw P Y F := ⟨X, hX, hF⟩
  rw [rhoHat, dif_pos hex]
  exact ρ.property hex.choose hex.choose_spec.1 X hX
    (fun x => (hex.choose_spec.2 x).trans (hF x).symm)

/-- The actual pushforward law. Outside measurable random variables a harmless
constant law totalizes the function; every theorem restricts risks to L∞. -/
noncomputable def law (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) :
    ProbabilityMeasure ℝ := by
  classical
  exact if hX : Measurable X then ⟨P.map X, P.isProbabilityMeasure_map hX.aemeasurable⟩
         else constantLaw 0

/-- p. 16: the generated risk, defined only for a law-invariant input. -/
noncomputable def generated (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : LawInvariantRisk P) (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ)
    (X : Ω → ℝ) : ℝ :=
  rhoHat P ρ (T (law P X))

/-- p. 16: VaR at an interior confidence level. -/
noncomputable def valueAtRisk (p : ℝ) (F : ProbabilityMeasure ℝ) : ℝ := leftQuantile F p

/-- p. 16: ES, used only for 0 < p < 1. The omitted integration endpoints have
Lebesgue measure zero; quantile values at endpoints are never used. -/
noncomputable def expectedShortfall (p : ℝ) (F : ProbabilityMeasure ℝ) : ℝ :=
  (1 - p)⁻¹ * ∫ t in Set.Ioo p (1 : ℝ), leftQuantile F t

/-- The law-invariant ES input permits a direct distributional evaluation of its transform. -/
noncomputable def generatedES (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) (p : ℝ) (X : Ω → ℝ) : ℝ :=
  expectedShortfall p (T (law P X))

end DistTransform.Distortion.Supplement



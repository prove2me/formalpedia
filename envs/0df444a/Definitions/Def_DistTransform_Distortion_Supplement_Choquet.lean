-- Prove2me | Definitions.Def_DistTransform_Distortion_Supplement_Choquet
-- name    : DistTransform_Distortion_Supplement_Choquet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T13:03:27.746803+00:00
-- url     : https://prove2.me/theorems/f853adc6-79e2-46a0-984e-de680cea776d
-- title:
--   Eq. (7)–(8) — H, Choquet integrals and ordered families
-- statement:
--   Let H consist of the increasing functions h:[0,1]→ℝ with h(0)=0 and h(1)=1. Continuity is not required. For a bounded distribution F define
--
--   $$
--   I_h(F)=\int_{-\infty}^{0}\bigl(h(1-F(x))-1\bigr)\,dx+\int_{0}^{\infty}h(1-F(x))\,dx.
--   $$
--
--   A family (h_p)_{0<p<1} is pointwise increasing if each h_p belongs to H and h_{p_1}(t)≤h_{p_2}(t) whenever p_1≤p_2 and t∈[0,1]. The family represents an output law G at input F when
--
--   $$
--   G^{-1}(p)=I_{h_p}(F)\quad\text{for Lebesgue-almost every }p\in(0,1).
--   $$
--
--   This interface preserves arbitrary discontinuous members of H and permits a separate exceptional null set for each input distribution. For h∈H and F∈M∞, both integrands are bounded measurable functions vanishing outside bounded intervals, so both integrals are ordinary finite Lebesgue integrals.
--
--   **Formalization Note** Functions are defined on ℝ but constrained only on [0,1]; the family is constrained only for p∈(0,1). This does not impose any behavior outside the source domain. The point 0 in the split integral has Lebesgue measure zero.
-- source:
--   Liu, Schied and Wang, Distributional transforms, probability distortions, and their applications, SSRN 3419388 (version of March 19, 2020), p. 11, H, Eq. (7), Theorem 2 and Eq. (8)

import Mathlib
import Definitions.Def_DistTransform_Distortion_Supplement_Algebra

namespace DistTransform.Distortion.Supplement

open MeasureTheory ProbabilityTheory

/-- p. 11: H has no continuity requirement. Values off [0,1] are irrelevant. -/
def IsH (h : ℝ → ℝ) : Prop :=
  MonotoneOn h (Set.Icc 0 1) ∧ h 0 = 0 ∧ h 1 = 1

/-- Eq. (7), p. 11. For h ∈ H and bounded laws both Lebesgue integrals
are finite: the integrands are measurable, bounded, and vanish outside a bounded interval. -/
noncomputable def choquet (h : ℝ → ℝ) (F : ProbabilityMeasure ℝ) : ℝ :=
  (∫ x in Set.Iic (0 : ℝ), (h (1 - cdf (F : Measure ℝ) x) - 1)) +
    ∫ x in Set.Ioi (0 : ℝ), h (1 - cdf (F : Measure ℝ) x)

/-- p. 11: one family in H, ordered pointwise in the interior level p. -/
def IsOrderedFamily (h : ℝ → ℝ → ℝ) : Prop :=
  (∀ p ∈ Set.Ioo (0 : ℝ) 1, IsH (h p)) ∧
    ∀ p₁ ∈ Set.Ioo (0 : ℝ) 1, ∀ p₂ ∈ Set.Ioo (0 : ℝ) 1,
      p₁ ≤ p₂ → ∀ t ∈ Set.Icc (0 : ℝ) 1, h p₁ t ≤ h p₂ t

/-- Eq. (8): the exceptional null set is allowed to depend on F. -/
def Represents (h : ℝ → ℝ → ℝ) (F G : ProbabilityMeasure ℝ) : Prop :=
  ∀ᵐ p ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), leftQuantile G p = choquet (h p) F

end DistTransform.Distortion.Supplement



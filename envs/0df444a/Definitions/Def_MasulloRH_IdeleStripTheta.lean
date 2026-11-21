-- Prove2me | Definitions.Def_MasulloRH_IdeleStripTheta
-- name    : MasulloRH_IdeleStripTheta
-- status  : Definition
-- author  : @marozols
-- created : 2026-11-21T03:46:50.714083+00:00
-- url     : https://prove2.me/theorems/102f9770-ddf3-40b5-8310-ef043975669e
-- title:
--   Strip-weighted spherical theta annihilator on the rational idèle class quotient
-- statement:
--   On the actual quotient of the rational idèles by the principal idèles, take all genuine adelic Schwartz–Bruhat theta profiles, average over the finite units and pull the logarithmic strip weight back along the idèle norm. The annihilator is the orthogonal complement of these conjugate rows inside the spherical sector. The weak convolution formula uses right translation by the positive-real section and tests against every ambient square-integrable function.
-- source:
--   Masullo, The Music of the Primes, rational character component of §§9–10. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloRH_RationalClassThetaSpace
import Definitions.Def_MasulloRH_WeightedStripJetSpace

open MeasureTheory NumberField IsDedekindDomain
open MasulloRH.RationalFinite MasulloRH.RationalClass
open scoped InnerProductSpace

namespace MasulloRH
noncomputable section

variable [MeasurableSpace RationalClass.Ad] [MeasurableSpace RationalFinite.K] [MeasurableSpace RationalClass.C]

/-- Conjugate theta rows cut out by admissible global Schwartz–Bruhat tests, with
the reciprocal strip weight pulled back along the logarithmic idèle norm. -/
def rationalClassStripThetaRows (μ : Measure Ad) (κ : Measure K) (ν : Measure C) (b p : ℝ) :
    Set (Lp ℂ 2 ν) :=
  {v | ∃ F ∈ AdelicFourier.schwartzBruhat ℚ, F 0=0 ∧ (∫ a,F a ∂μ)=0 ∧
    (v:C→ℂ) =ᵐ[ν] fun z => (starRingEnd ℂ)
      (((1/rationalStripWeight b p (logNorm z):ℝ):ℂ) *
        ((Real.exp (logNorm z/2):ℂ)*sphericalTheta κ F z))}

/-- The joint theta annihilator inside the spherical sector of the idèle class quotient. -/
def rationalClassStripThetaAnnihilator (μ : Measure Ad) (κ : Measure K) (ν : Measure C) (b p : ℝ) :
    Submodule ℂ (Lp ℂ 2 ν) :=
  rationalClassSpherical κ ν ⊓ (Submodule.span ℂ (rationalClassStripThetaRows μ κ ν b p))ᗮ

instance rationalClassStripThetaAnnihilator_completeSpace (μ : Measure Ad) (κ : Measure K) (ν : Measure C)
    (b p : ℝ) : CompleteSpace (rationalClassStripThetaAnnihilator μ κ ν b p) := by
  have hc : IsClosed (rationalClassStripThetaAnnihilator μ κ ν b p : Set (Lp ℂ 2 ν)) :=
    (Submodule.isClosed_topologicalClosure _).inter (Submodule.isClosed_orthogonal _)
  exact hc.completeSpace_coe

/-- Weak convolution by the positive-real section, paired against arbitrary ambient
quotient vectors. The scalar cocycle uses the strip weight at the two class norms. -/
def IsRationalClassStripThetaConvolution (μ : Measure Ad) (κ : Measure K) (ν : Measure C) (b p : ℝ)
    (ray : ℝ→C) (φ : ℝ→ℂ) (T : rationalClassStripThetaAnnihilator μ κ ν b p →L[ℂ]
      rationalClassStripThetaAnnihilator μ κ ν b p) : Prop :=
  ∀ (u : rationalClassStripThetaAnnihilator μ κ ν b p) (g : Lp ℂ 2 ν),
    ⟪g,(T u : Lp ℂ 2 ν)⟫_ℂ =
      ∫ y : ℝ, φ (Real.exp y) * ∫ z : C, (starRingEnd ℂ) (g z) *
        (((rationalStripWeight b p (logNorm z)/rationalStripWeight b p (logNorm (z*ray y)):ℝ):ℂ) *
          (u : Lp ℂ 2 ν) (z*ray y)) ∂ν

end
end MasulloRH



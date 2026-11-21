-- Prove2me | Definitions.Def_MasulloRH_StripThetaAnnihilator
-- name    : MasulloRH_StripThetaAnnihilator
-- status  : Definition
-- author  : @marozols
-- created : 2026-11-21T03:34:25.384423+00:00
-- url     : https://prove2.me/theorems/ce894be1-df6e-4ff3-ad62-27af26bccc66
-- title:
--   The actual rational theta annihilator in weighted L² on a logarithmic strip
-- statement:
--   Take the orthogonal complement of the closed span of the reciprocal-weight profiles of all rational two-moment Schwartz theta tests. Weak physical convolution is defined by logarithmic translation paired with every ambient L² function. The positive exponential half-width b and the Sobolev weight exponent p are independent.
-- source:
--   Masullo, The Music of the Primes, rational spherical specialization of §§9–10, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. Extends the zero-width rationalThetaAnnihilator and uses the weight of definition 8d4cb7cb.

import Definitions.Def_MasulloRH_WeightedStripJetSpace

open MeasureTheory Filter
open scoped SchwartzMap InnerProductSpace

namespace MasulloRH

/-- The rational spherical theta annihilator on a strip of half-width b and polynomial
weight exponent p in the logarithmic L² realization. -/
noncomputable def rationalStripThetaAnnihilator (b p : ℝ) : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  (Submodule.span ℂ {f : Lp ℂ 2 (volume : Measure ℝ) |
    ∃ g : 𝓢(ℝ,ℂ), g 0=0 ∧ (∫ x : ℝ,g x)=0 ∧ (f:ℝ→ℂ) =ᵐ[volume] fun x : ℝ =>
      (starRingEnd ℂ) (((1/rationalStripWeight b p x:ℝ):ℂ) *
        ((Real.exp (x/2):ℂ)*∑' n : ℤ,g ((n:ℝ)*Real.exp x)))})ᗮ

noncomputable instance rationalStripThetaAnnihilator_completeSpace (b p : ℝ) :
    CompleteSpace (rationalStripThetaAnnihilator b p) := by unfold rationalStripThetaAnnihilator; infer_instance

/-- Physical logarithmic convolution on the actual theta annihilator, paired against
an arbitrary ambient L² function. -/
def IsRationalStripThetaConvolution (b p : ℝ) (φ : ℝ→ℂ)
    (T : rationalStripThetaAnnihilator b p →L[ℂ] rationalStripThetaAnnihilator b p) : Prop :=
  ∀ (u : rationalStripThetaAnnihilator b p) (g : Lp ℂ 2 (volume : Measure ℝ)),
    ⟪g,(T u : Lp ℂ 2 (volume : Measure ℝ))⟫_ℂ =
      ∫ y : ℝ, φ (Real.exp y) * ∫ x : ℝ, (starRingEnd ℂ) (g x) *
        (((rationalStripWeight b p x/rationalStripWeight b p (x+y):ℝ):ℂ) *
          (u : Lp ℂ 2 (volume : Measure ℝ)) (x+y))

end MasulloRH



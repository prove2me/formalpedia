-- Prove2me | Definitions.Def_MasulloRH_WeightedStripJetSpace
-- name    : MasulloRH_WeightedStripJetSpace
-- status  : Definition
-- author  : @marozols
-- created : 2026-11-21T03:08:15.415525+00:00
-- url     : https://prove2.me/theorems/8d4cb7cb-40fa-4030-9c21-83d16927520f
-- title:
--   The closed space of physical weighted zeta jets on a logarithmic strip
-- statement:
--   For half-width b and Sobolev exponent p, take the closed span in ordinary log-coordinate L² of the exponential-polynomial modes at the nontrivial zeros of zeta, after multiplication by (1+x²)^(-p/2) exp(-b|x|). Every jet below the zero multiplicity is admitted in the open strip. On the boundary the order must also satisfy r+1/2<p. Physical multiplicative convolution is defined weakly against every ambient L² function by the actual translated weight ratio.
-- source:
--   A. M. Masullo, The Music of the Primes, §§9–10, rational specialization of the logarithmic spectral jet construction, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Mathlib

open MeasureTheory Filter
open scoped InnerProductSpace

namespace MasulloRH

/-- Square root of the logarithmic strip weight on the dual side. -/
noncomputable def rationalStripWeight (b p x : ℝ) : ℝ :=
  (1+x^2)^(-p/2) * Real.exp (-b*|x|)

/-- The closure in ordinary L² of the weighted exponential-polynomial modes at
nontrivial zeta zeros. At a boundary zero only orders satisfying the strict
weighted L² threshold are included. -/
noncomputable def rationalStripJetSpace (b p : ℝ) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  (Submodule.span ℂ {f : Lp ℂ 2 (volume : Measure ℝ) |
    ∃ z : ℂ, riemannZeta z=0 ∧ 0<z.re ∧ z.re<1 ∧ ∃ r : ℕ,
      r < analyticOrderNatAt riemannZeta z ∧
      (|z.re-1/2|<b ∨ (|z.re-1/2|=b ∧ (r:ℝ)+1/2<p)) ∧
      (f : ℝ→ℂ) =ᵐ[volume] fun x : ℝ =>
        (rationalStripWeight b p x : ℂ)*(x:ℂ)^r*Complex.exp ((z-1/2)*x)}).topologicalClosure

noncomputable instance rationalStripJetSpace_completeSpace (b p : ℝ) :
    CompleteSpace (rationalStripJetSpace b p) := by
  unfold rationalStripJetSpace
  infer_instance

/-- Weak logarithmic convolution, paired with every ambient L² vector. -/
def IsRationalStripJetConvolution (b p : ℝ) (φ : ℝ→ℂ)
    (T : rationalStripJetSpace b p →L[ℂ] rationalStripJetSpace b p) : Prop :=
  ∀ (u : rationalStripJetSpace b p) (g : Lp ℂ 2 (volume : Measure ℝ)),
    ⟪g,(T u : Lp ℂ 2 (volume : Measure ℝ))⟫_ℂ =
      ∫ y : ℝ, φ (Real.exp y) * ∫ x : ℝ, (starRingEnd ℂ) (g x) *
        (((rationalStripWeight b p x/rationalStripWeight b p (x+y):ℝ):ℂ) *
          (u : Lp ℂ 2 (volume : Measure ℝ)) (x+y))

end MasulloRH



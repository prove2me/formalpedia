-- Prove2me | Definitions.Def_OAIQ098E018
-- name    : OAIQ098E018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T05:24:34.31566+00:00
-- url     : https://prove2.me/theorems/3c1cfb58-045b-458a-9da8-b4ce7370a46c
-- title:
--   Definitions bundle OAIQ098E018 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 36 declarations of OpenAI's Lean: 36 definitions. The definitions and types are `OAI.SharpPlanar.IntegerBasis.basisAlpha`, `OAI.SharpPlanar.IntegerBasis.basisBeta`, `OAI.SharpPlanar.IntegerBasis.basisFunction`, `OAI.SharpPlanar.IntegerBasis.basisMoment`, `OAI.SharpPlanar.IntegerBasis.momentRuleValue`, `OAI.SharpPlanar.IntegerBasis.phase12`, `OAI.SharpPlanar.IntegerBasis.spectralCoefficient`, `OAI.SharpPlanar.IntegerBasis.waveAmplitude`, `OAI.SharpPlanar.IntegerGrid.quadraturePoint`, `OAI.SharpPlanar.IntegerIntervals.expHorner`, `OAI.SharpPlanar.IntegerIntervals.pointLambda`, `OAI.SharpPlanar.IntegerIntervals.pointZ`, `OAI.SharpPlanar.P`, `OAI.SharpPlanar.coeffMass`, `OAI.SharpPlanar.complexBasis`, `OAI.SharpPlanar.complexBasisMoment`, `OAI.SharpPlanar.complexLambda`, `OAI.SharpPlanar.complexTransformedFactor`, `OAI.SharpPlanar.complexU`, `OAI.SharpPlanar.complexV`, `OAI.SharpPlanar.complexZ`, `OAI.SharpPlanar.cosTable`, `OAI.SharpPlanar.diskAffine`, `OAI.SharpPlanar.diskCenter`, `OAI.SharpPlanar.fejerAngle`, `OAI.SharpPlanar.fejerNode`, `OAI.SharpPlanar.fejerPartial`, `OAI.SharpPlanar.fejerPolynomial`, `OAI.SharpPlanar.fejerWeight`, `OAI.SharpPlanar.finiteDensity`, `OAI.SharpPlanar.pieceIntegral`, `OAI.SharpPlanar.pieceRule`, `OAI.SharpPlanar.rootPhase`, `OAI.SharpPlanar.sinTable`, `OAI.SharpPlanar.singleCoefficient`, `OAI.SharpPlanar.taylorPolynomial`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_BasisIntervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean), [`PlanarPacking_Cardinal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean), [`PlanarPacking_Fejer`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Fejer.lean), [`PlanarPacking_Grid`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Grid.lean), [`PlanarPacking_Intervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean), [`PlanarPacking_Nodes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Nodes.lean), [`PlanarPacking_Quadrature`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean), [`PlanarPacking_Roots`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Roots.lean).
--
--   **Imports.** It imports the bundle `OAIQ098E001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098E028`; the statements `OAI.SharpPlanar.D_as_table_e`, `OAI.SharpPlanar.IntegerIntervals.expHorner_eq_e`, `OAI.SharpPlanar.IntegerIntervals.exp_small_error_e`, `OAI.SharpPlanar.Pcoeff_norm_e`, `OAI.SharpPlanar.Q_as_table_e`, `OAI.SharpPlanar.analytic_taylor_error_e`, `OAI.SharpPlanar.complexBasis_rule_error_e`, `OAI.SharpPlanar.complexLambda_differentiableAt_e`, `OAI.SharpPlanar.complexTransformedFactor_differentiableAt_e`, `OAI.SharpPlanar.complexTransformedFactor_disk_bound_e`, `OAI.SharpPlanar.complexU_disk_bound_e`, `OAI.SharpPlanar.complexV_disk_bound_e`, `OAI.SharpPlanar.diskAffine_mem_e`, `OAI.SharpPlanar.disk_coordinate_bounds_e`, `OAI.SharpPlanar.disk_delta_bounds_e`, `OAI.SharpPlanar.disk_denominator_lower_e`, `OAI.SharpPlanar.disk_denominator_ne_e`, `OAI.SharpPlanar.disk_frequency_distance_e`, `OAI.SharpPlanar.disk_lambda_bound_e`, `OAI.SharpPlanar.disk_phase_bound_e`, `OAI.SharpPlanar.disk_z_bound_e`, `OAI.SharpPlanar.disk_z_imaginary_e`, `OAI.SharpPlanar.disk_z_imaginary_simple_e`, `OAI.SharpPlanar.fejerPolynomial_degree_e`, `OAI.SharpPlanar.fejerPolynomial_eval_e`, `OAI.SharpPlanar.fejerWeight_pos_e`, `OAI.SharpPlanar.fejer_analytic_average_error_e`, `OAI.SharpPlanar.fejer_cheb_integral_e`, `OAI.SharpPlanar.fejer_exact_complex_e`, `OAI.SharpPlanar.fejer_exact_e`, `OAI.SharpPlanar.fejer_exact_monomial_e`, `OAI.SharpPlanar.fejer_integral_even_e`, `OAI.SharpPlanar.fejer_integral_odd_e`, `OAI.SharpPlanar.fejer_integral_zero_e`, `OAI.SharpPlanar.fejer_polynomial_integral_e`, `OAI.SharpPlanar.fejer_weighted_orthogonal_e`, `OAI.SharpPlanar.finiteDensity_disk_bound_e`, `OAI.SharpPlanar.pieceIntegral_affine_e`, `OAI.SharpPlanar.piece_rule_error_scaling_e`, `OAI.SharpPlanar.taylorPolynomial_zero_e`, `OAI.SharpPlanar.transformedIntegrand_analytic_e`, `OAI.SharpPlanar.transformedIntegrand_disk_bound_e`, `OAI.SharpPlanar.transformedMoment_piece_average_error_e`, `OAI.SharpPlanar.transformedMoment_piece_error_e`, `OAI.SharpPlanar.transformedMoment_rule_error_e` and `OAI.SharpPlanar.trig_table_e`; the proofs of `OAI.SharpPlanar.D_0_e`, `OAI.SharpPlanar.D_1_e`, `OAI.SharpPlanar.D_3_e`, `OAI.SharpPlanar.D_4_e`, `OAI.SharpPlanar.D_7_e`, `OAI.SharpPlanar.D_9_e`, `OAI.SharpPlanar.D_as_table_e`, `OAI.SharpPlanar.IntegerIntervals.expHorner_eq_e`, `OAI.SharpPlanar.IntegerIntervals.exp_small_error_e`, `OAI.SharpPlanar.Pcoeff_norm_e`, `OAI.SharpPlanar.Q_0_e`, `OAI.SharpPlanar.Q_1_e`, `OAI.SharpPlanar.Q_3_e`, `OAI.SharpPlanar.Q_4_e`, `OAI.SharpPlanar.Q_7_e`, `OAI.SharpPlanar.Q_9_e`, `OAI.SharpPlanar.Q_as_table_e`, `OAI.SharpPlanar.Scoords_mem_e`, `OAI.SharpPlanar.Slinear_bound_e`, `OAI.SharpPlanar.analytic_taylor_error_e`, `OAI.SharpPlanar.complexBasis_rule_error_e`, `OAI.SharpPlanar.complexLambda_differentiableAt_e`, `OAI.SharpPlanar.complexTransformedFactor_differentiableAt_e`, `OAI.SharpPlanar.complexTransformedFactor_disk_bound_e`, `OAI.SharpPlanar.complexU_disk_bound_e`, `OAI.SharpPlanar.complexV_disk_bound_e`, `OAI.SharpPlanar.diskAffine_mem_e`, `OAI.SharpPlanar.disk_coordinate_bounds_e`, `OAI.SharpPlanar.disk_delta_bounds_e`, `OAI.SharpPlanar.disk_denominator_lower_e`, `OAI.SharpPlanar.disk_denominator_ne_e`, `OAI.SharpPlanar.disk_frequency_distance_e`, `OAI.SharpPlanar.disk_lambda_bound_e`, `OAI.SharpPlanar.disk_phase_bound_e`, `OAI.SharpPlanar.disk_z_bound_e`, `OAI.SharpPlanar.disk_z_imaginary_e`, `OAI.SharpPlanar.disk_z_imaginary_simple_e`, `OAI.SharpPlanar.fejerPolynomial_degree_e`, `OAI.SharpPlanar.fejerPolynomial_eval_e`, `OAI.SharpPlanar.fejerWeight_pos_e`, `OAI.SharpPlanar.fejer_analytic_average_error_e`, `OAI.SharpPlanar.fejer_cheb_integral_e`, `OAI.SharpPlanar.fejer_exact_complex_e`, `OAI.SharpPlanar.fejer_exact_e`, `OAI.SharpPlanar.fejer_exact_monomial_e`, `OAI.SharpPlanar.fejer_integral_even_e`, `OAI.SharpPlanar.fejer_integral_odd_e`, `OAI.SharpPlanar.fejer_integral_zero_e`, `OAI.SharpPlanar.fejer_polynomial_integral_e`, `OAI.SharpPlanar.fejer_weighted_orthogonal_e`, `OAI.SharpPlanar.finiteDensity_disk_bound_e`, `OAI.SharpPlanar.pieceIntegral_affine_e`, `OAI.SharpPlanar.piece_rule_error_scaling_e`, `OAI.SharpPlanar.positive_coeff_mass_e`, `OAI.SharpPlanar.taylorPolynomial_zero_e`, `OAI.SharpPlanar.transformedIntegrand_analytic_e`, `OAI.SharpPlanar.transformedIntegrand_disk_bound_e`, `OAI.SharpPlanar.transformedJets_summable_e`, `OAI.SharpPlanar.transformedMoment_piece_average_error_e`, `OAI.SharpPlanar.transformedMoment_piece_error_e`, `OAI.SharpPlanar.transformedMoment_rule_error_e` and `OAI.SharpPlanar.trig_table_e`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098E001

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

noncomputable def P (s : ℝ) : ℝ :=
  ∏ a ∈ residues, (2 * Real.sin (Real.pi * (s - a) / 12)) ^ 2


def coeffMass : ℕ → ℝ
  | 0 => 5
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 1
  | 5 => 2
  | 6 => 1
  | _ => 0

end SharpPlanar

namespace SharpPlanar
open Complex

noncomputable def complexLambda (t : ℂ) : ℂ :=
  Complex.I / ((b:ℂ) * (t+Complex.I*(h:ℂ)))
noncomputable def complexZ (t : ℂ) : ℂ :=
  -(B:ℂ)/(t+Complex.I*(h:ℂ))-Complex.I*(h:ℂ)


noncomputable def diskCenter (j : ℕ) : ℝ := (2*(j:ℝ)+1)/12

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set


noncomputable def complexU (n j : ℕ) (t : ℂ) : ℂ :=
  -2 * (Real.pi:ℂ)^2 * Complex.exp (-Complex.I*Real.pi*t*n) *
    ∑ l ∈ Finset.Icc (j+1) 6,
      ((l:ℂ)/6-t)*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)
noncomputable def complexV (n j : ℕ) (t : ℂ) : ℂ :=
  2*Complex.I*Real.pi*Complex.exp (-Complex.I*Real.pi*t*n) *
    ∑ l ∈ Finset.Icc (j+1) 6,
      Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)

noncomputable def finiteDensity (c d : ℕ → ℝ) (j : ℕ) (t : ℂ) : ℂ :=
  ∑ n ∈ Finset.range 101, ((c n:ℂ)*complexU n j t + (d n:ℂ)*complexV n j t)

end SharpPlanar

namespace SharpPlanar
open Complex

noncomputable def complexTransformedFactor (m y : ℝ) (ell : ℕ) (t : ℂ) : ℂ :=
  complexLambda t * Complex.exp (Complex.I*Real.pi*complexZ t*m) *
    (Complex.I*Real.pi*complexZ t*y)^ell / (ell.factorial:ℂ)

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar
namespace IntegerIntervals

noncomputable def expHorner (z : ℂ) (k : ℕ) : ℕ → ℂ
  | 0 => (k.factorial:ℂ)⁻¹
  | n+1 => (k.factorial:ℂ)⁻¹ + z*expHorner z (k+1) n

end IntegerIntervals
end SharpPlanar

namespace SharpPlanar.IntegerIntervals

-- These are exactly lambda,z from fourier:frequencies, restricted to real t.
noncomputable def pointLambda (t : ℝ) : ℂ :=
  Complex.I / (((Real.sqrt 3/2:ℝ):ℂ) * ((t:ℂ)+Complex.I*(2/5:ℂ)))
noncomputable def pointZ (t : ℝ) : ℂ :=
  -(4/3:ℂ) / ((t:ℂ)+Complex.I*(2/5:ℂ)) - Complex.I*(2/5:ℂ)

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Roots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Certified roots of unity

Integer enclosures for the 1024th roots of unity, obtained from a certified
Taylor approximation and repeated squaring.
-/

namespace SharpPlanar
noncomputable def rootPhase (n : ℕ) : ℂ := Complex.exp (Complex.I*Real.pi*((n:ℂ)/512))


end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Fejer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fejér quadrature enclosures

Certified nodes and weights for the 256-node cosine quadrature rule.
-/

namespace SharpPlanar
noncomputable def fejerAngle (v : ℕ) : ℝ := Real.pi*((v:ℝ)+1/2)/256
noncomputable def fejerNode (v : ℕ) : ℝ := Real.cos (fejerAngle v)
noncomputable def fejerWeight (v : ℕ) : ℝ :=
  (1-2*∑ a ∈ Finset.Icc (1:ℕ) 127,
    Real.cos (2*(a:ℝ)*fejerAngle v)/(4*(a:ℝ)^2-1))/256


end SharpPlanar

namespace SharpPlanar
open IntegerIntervals

noncomputable def fejerPartial (v N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    Real.cos (2*((k+1:ℕ):ℝ)*fejerAngle v)/(4*((k+1:ℕ):ℝ)^2-1)

end SharpPlanar


end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Quadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev

namespace SharpPlanar


noncomputable def fejerPolynomial :=
  1-∑ a ∈ Finset.Icc (1:ℕ) 127, (2/(4*(a:ℝ)^2-1)) • T ℝ (2*a)

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar

noncomputable def taylorPolynomial (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, (n.factorial : ℂ)⁻¹*iteratedDeriv n f c*(z-c)^n

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

noncomputable def diskAffine (j : ℕ) (w : ℂ) : ℂ := (diskCenter j:ℂ)+w/12

end SharpPlanar

namespace SharpPlanar
open MeasureTheory

noncomputable def pieceIntegral (F : ℂ → ℂ) (j : ℕ) : ℂ :=
  ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, F t
noncomputable def pieceRule (F : ℂ → ℂ) (j : ℕ) : ℂ :=
  (1/6:ℂ) * ∑ v : Fin 256, (fejerWeight v.val:ℂ) *
    F (diskAffine j (fejerNode v.val))

end SharpPlanar

namespace SharpPlanar
open MeasureTheory

noncomputable def singleCoefficient (n : ℕ) (k : ℕ) : ℝ := if k=n then 1 else 0

noncomputable def complexBasis (d : Bool) (n j : ℕ) (t : ℂ) : ℂ :=
  if d then complexV n j t else complexU n j t
noncomputable def complexBasisMoment (d e : Bool) (n j m : ℕ) (t : ℂ) : ℂ :=
  complexBasis d n j t * complexTransformedFactor m 1 (if e then 1 else 0) t

end SharpPlanar


end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

noncomputable def phase12 (n : ℕ) : ℂ := Complex.exp (Complex.I*Real.pi*((n:ℂ)/6))

noncomputable def spectralCoefficient (n l : ℕ) : ℂ :=
  Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

noncomputable def basisAlpha (n j : ℕ) : ℂ := ∑ l ∈ Finset.Icc (j+1) 6, spectralCoefficient n l
noncomputable def basisBeta (n j : ℕ) : ℂ :=
  ∑ l ∈ Finset.Icc (j+1) 6, ((l:ℂ)/6)*spectralCoefficient n l

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

noncomputable def basisFunction (d : Bool) (n j : ℕ) (t : ℝ) : ℂ :=
  if d then v n j t else u n j t
noncomputable def basisMoment (d e : Bool) (n j m : ℕ) (t : ℝ) : ℂ :=
  basisFunction d n j t * (lambda t*Complex.exp (Complex.I*Real.pi*z t*m)) *
    (if e then Complex.I*Real.pi*z t else 1)

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

noncomputable def momentRuleValue (t : ℕ → ℕ → ℝ) (w : ℕ → ℝ)
    (n m : ℕ) (d e : Bool) : ℂ :=
  ∑ j : Fin 6, (1/6:ℂ)*∑ v : Fin 256, (w v.val:ℂ)*
    basisMoment d e n j.val m (t j.val v.val)

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

noncomputable def waveAmplitude (d : Bool) (n j : ℕ) (t : ℝ) : ℂ :=
  if d then 2*Complex.I*Real.pi*basisAlpha n j
  else -2*(Real.pi:ℂ)^2*(basisBeta n j-(t:ℂ)*basisAlpha n j)

end SharpPlanar.IntegerBasis

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fourier quadrature grid

Certified rational enclosures for the quadrature points and their Fourier
kernels on each of the six subintervals.
-/

namespace SharpPlanar.IntegerGrid
open IntegerIntervals
noncomputable def quadraturePoint (j v : ℕ) : ℝ := (2*(j:ℝ)+1)/12+fejerNode v/12
end SharpPlanar.IntegerGrid

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

noncomputable def sinTable : ℕ → ℝ
  | 0 => 0 | 1 => 1/2 | 2 => b | 3 => 1 | 4 => b | 5 => 1/2
  | 6 => 0 | 7 => -1/2 | 8 => -b | 9 => -1 | 10 => -b | 11 => -1/2
  | _ => 0
noncomputable def cosTable : ℕ → ℝ
  | 0 => 1 | 1 => b | 2 => 1/2 | 3 => 0 | 4 => -1/2 | 5 => -b
  | 6 => -1 | 7 => -b | 8 => -1/2 | 9 => 0 | 10 => 1/2 | 11 => b
  | _ => 1

end SharpPlanar

end OAI
end



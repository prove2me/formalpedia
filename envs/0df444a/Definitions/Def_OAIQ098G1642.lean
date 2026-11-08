-- Prove2me | Definitions.Def_OAIQ098G1642
-- name    : OAIQ098G1642
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:47:09.298967+00:00
-- url     : https://prove2.me/theorems/d2654b45-3d7b-4a05-b0e5-cbc18b0f0755
-- title:
--   Definitions bundle OAIQ098G1642 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 17 definitions and 1 inductive type or structure. The definitions and types are `OAI.SharpPlanar.HasLatticePoisson`, `OAI.SharpPlanar.Pmoment`, `OAI.SharpPlanar.basisMoment`, `OAI.SharpPlanar.cardinalSeries`, `OAI.SharpPlanar.fixedPart`, `OAI.SharpPlanar.fixed₁`, `OAI.SharpPlanar.fixed₂`, `OAI.SharpPlanar.foldedU`, `OAI.SharpPlanar.foldedV`, `OAI.SharpPlanar.gaussianCoeff`, `OAI.SharpPlanar.gaussianSpectral`, `OAI.SharpPlanar.hexPoint`, `OAI.SharpPlanar.latticeDamping`, `OAI.SharpPlanar.latticePoint`, `OAI.SharpPlanar.qComplex`, `OAI.SharpPlanar.spectralGaussian`, `OAI.SharpPlanar.spectralParameter`, `OAI.SharpPlanar.tailList`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Cardinal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean), [`PlanarPacking_Certificate_TailCoefficients`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TailCoefficients.lean), [`PlanarPacking_DataSplit`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/DataSplit.lean), [`PlanarPacking_Entire`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean), [`PlanarPacking_FourierPairSupport`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FourierPairSupport.lean), [`PlanarPacking_HexLattice`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/HexLattice.lean), [`PlanarPacking_LatticeGaussian`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/LatticeGaussian.lean), [`PlanarPacking_LatticePoisson`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/LatticePoisson.lean).
--
--   **Imports.** It imports the published bundle `Def_PlanarPacking`; the bundle `OAIQ098G001` of this split; the published statement `OAI.SharpPlanar.tailScalar_summable_g`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1649`, `OAIQ098G1650` and `OAIQ098G1695`; the statements `OAI.SharpPlanar.Pmoment_norm_bound_g`, `OAI.SharpPlanar.directDensity_series_g`, `OAI.SharpPlanar.direct_positive_series_g`, `OAI.SharpPlanar.direct_spectral_bound_g` and `OAI.SharpPlanar.fullMoment_direct_g`; the proofs of `OAI.SharpPlanar.Pmoment_norm_bound_g`, `OAI.SharpPlanar.directDensity_series_g`, `OAI.SharpPlanar.direct_positive_series_g`, `OAI.SharpPlanar.direct_spectral_bound_g` and `OAI.SharpPlanar.fullMoment_direct_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_PlanarPacking
import Definitions.Def_OAIQ098G001
import Theorems.Thm_OAI_SharpPlanar_tailScalar_summable_g

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

noncomputable def fixed₁ (x : X) : CardinalData := ⟨-13/1000, 1, 11/25, x⟩
noncomputable def fixed₂ (x : X) : CardinalData := ⟨17/1000, 0, -46/125, x⟩

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entire
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal interpolation

The folded spectral representation gives the cardinal values and derivatives.
Gaussian damping then extends the radial cardinal functions to Schwartz functions.
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory



open MeasureTheory
open scoped ComplexConjugate

namespace SharpPlanar

noncomputable def foldedU (n : ℕ) (s : ℝ) : ℝ :=
  (∑ j ∈ Finset.range 6, ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
    u n j t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)).re

noncomputable def foldedV (n : ℕ) (s : ℝ) : ℝ :=
  (∑ j ∈ Finset.range 6, ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
    v n j t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)).re

end SharpPlanar

namespace SharpPlanar

noncomputable def Pmoment (ell : ℕ) (s : ℝ) : ℝ :=
  (Pcoeff 0 * (0 : ℂ)^ell + ∑ j ∈ Finset.Icc (1 : ℕ) 6,
    2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^ell *
      Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*s)).re

end SharpPlanar



open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff

namespace SharpPlanar
open MeasureTheory Set

noncomputable def basisMoment (sec : Bool) (n ell : ℕ) (s : ℝ) : ℝ :=
  (∑ j ∈ Finset.range 6, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
    (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)).re

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

noncomputable def cardinalSeries (p : CardinalData) (ell : ℕ) (s : ℝ) : ℝ :=
  p.C*Pmoment ell s + p.c₀*basisMoment false 0 ell s + p.d₀*basisMoment true 0 ell s +
    ∑' n : Node, (p.x (n,false)*basisMoment false n.val ell s +
      p.x (n,true)*basisMoment true n.val ell s)

end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap


open scoped SchwartzMap

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_DataSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed and summable parts of cardinal data

Splitting cardinal data separates the fixed coefficients from the absolutely summable interpolation unknowns.
-/

namespace SharpPlanar
open MeasureTheory
noncomputable def fixedPart (p : CardinalData) : CardinalData := ⟨p.C,p.c₀,p.d₀,0⟩
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TailCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tails of the interpolation coefficients

Truncating a summable coefficient family contracts its norm. The finite rational
table for OpenAI's sharp planar Fourier construction bounds the tails of the
exact coefficients through the coefficient error estimate.
-/

namespace SharpPlanar
open Numerical
open scoped BigOperators
noncomputable def tailList (x : X) (N : ℕ) : X :=
  ⟨(fun k => if N<k.1.val then x k else 0), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs,apply_ite,abs_zero]
      using tailScalar_summable_g x N⟩
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FourierPairSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ComplexConjugate
open scoped FourierTransform RealInnerProductSpace

open scoped FourierTransform RealInnerProductSpace

namespace SharpPlanar


noncomputable def gaussianCoeff (t : ℝ) : ℂ :=
  (Real.pi : ℂ) * b * ((h : ℂ) - Complex.I*t)

noncomputable def spectralGaussian (t : ℝ) (x : Plane) : ℂ :=
  Complex.exp (-gaussianCoeff t * (‖x‖ : ℂ)^2)

end SharpPlanar

namespace SharpPlanar

noncomputable def gaussianSpectral (μ : Measure ℝ) (f : ℝ → ℂ) (x : Plane) : ℂ :=
  ∫ t, spectralGaussian t x * f t ∂μ

noncomputable def qComplex (p : CardinalData) (x : Plane) : ℂ :=
  gaussianSpectral (Measure.dirac 0) (fun _ => (p.C : ℂ)*Pcoeff 0) x +
    (∑ j ∈ Finset.Icc (1 : ℕ) 6,
      gaussianSpectral (Measure.dirac ((j : ℝ)/6))
        (fun _ => 2*(p.C : ℂ)*Pcoeff j) x) +
    (∑ j ∈ Finset.range 6,
      gaussianSpectral (volume.restrict (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6)))
        (density p j) x)

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HexLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
noncomputable def hexPoint (v : ℤ×ℤ) : Plane :=
  WithLp.toLp 2 ![((v.1:ℝ)+(v.2:ℝ)/2)/Real.sqrt b, Real.sqrt b*(v.2:ℝ)]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_LatticeGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
noncomputable def latticePoint (p : ℤ×ℤ) : Plane := hexPoint (p.2,p.1)
noncomputable def spectralParameter (t : ℝ) : ℂ := (b:ℂ)*((h:ℂ)-Complex.I*t)
noncomputable def latticeDamping (p : ℤ×ℤ) : ℝ :=
  Real.exp (-Real.pi*b*h*‖latticePoint p‖^2)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_LatticePoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
structure HasLatticePoisson (f : Plane→ℂ) : Prop where
  integrable : Integrable f
  summable : Summable (fun p : ℤ×ℤ => f (latticePoint p))
  fourier_summable : Summable (fun p : ℤ×ℤ => 𝓕 f (latticePoint p))
  eq : (∑' p : ℤ×ℤ, f (latticePoint p))=∑' p : ℤ×ℤ, 𝓕 f (latticePoint p)
end SharpPlanar

end OAI
end



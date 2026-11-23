-- Prove2me | Definitions.Def_DedekindZeta_GammaIntegral
-- name    : DedekindZeta_GammaIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T00:23:49.26704+00:00
-- url     : https://prove2.me/theorems/7d010cc7-2dd5-432f-9428-767f04925378
-- title:
--   Gamma Integral
-- statement:
--   Definitions and structural lemmas for Gamma Integral, from Mathlib Initiative and contributors's pinned A real sum-product counterexample conditional on Martinet’s tower theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
namespace DedekindZeta.GammaIntegral
open Classical
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open Classical in
/-- The standard multiplicative Haar measure `d^*x` on `K_ℝ^*`, written as a
density against the additive Lebesgue measure `volume` on `K_ℝ`:
`d^*x = (2/π)^{r₂} · |N(x)|^{-1} · dx`. The factor `|N(x)|^{-1} = ∏_w
|x_w|^{-mult w}` turns `dx_w` into the one-dimensional multiplicative Haar
`dx_w/|x_w|` (real) and `dλ_w/|z_w|²` (complex); the constant `(2/π)^{r₂}` is the
the standard treatment per-complex-place normalisation that pins the complex factor to `L_ℂ`.
The density vanishes on the measure-zero locus `N(x) = 0`, so the measure lives
on `K_ℝ^*`. -/
def mulHaar :=
  volume.withDensity fun x : mixedEmbedding.mixedSpace K =>
    ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹)
def gaussian (x : mixedEmbedding.mixedSpace K) : ℝ :=
  Real.exp (-Real.pi * ∑ w : InfinitePlace K, (mult w : ℝ) * normAtPlace w x ^ 2)
def gammaIntegral (f : mixedEmbedding.mixedSpace K → ℂ) (s : ℂ) : ℂ :=
  ∫ x, f x * (mixedEmbedding.norm x : ℂ) ^ s ∂(mulHaar K)
def gammaReal (s : ℂ) : ℂ :=
  ∫ x : ℝ, Real.exp (-Real.pi * x ^ 2) * (((|x| : ℝ) : ℂ)) ^ s
    ∂(volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹)
def gammaComplex (s : ℂ) : ℂ :=
  ∫ z : ℂ, Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * (‖z‖ : ℂ) ^ (2 * s)
    ∂(volume.withDensity fun z : ℂ => ENNReal.ofReal (2 / Real.pi * (‖z‖ ^ 2)⁻¹))
def realFactor (s : ℂ) (t : ℝ) : ℂ :=
  (|t|⁻¹ : ℝ) • (Real.exp (-Real.pi * t ^ 2) * (((|t| : ℝ) : ℂ)) ^ s)
def complexFactor (s : ℂ) (z : ℂ) : ℂ :=
  (2 / Real.pi * (‖z‖ ^ 2)⁻¹ : ℝ) •
    (Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * (‖z‖ : ℂ) ^ (2 * s))
def I (s : ℂ) : ℂ := gammaIntegral K (fun x => (gaussian K x : ℂ)) s
end
end DedekindZeta.GammaIntegral
namespace DedekindZeta
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
variable {K : Type*} [Field K] [NumberField K]
noncomputable section
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
end
end DedekindZeta
namespace DedekindZeta.GammaIntegral
open DedekindZeta DedekindZeta.Theta
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped nonZeroDivisors
end
end DedekindZeta.GammaIntegral



-- Prove2me | Definitions.Def_DedekindZeta_ConeRadialReduction
-- name    : DedekindZeta_ConeRadialReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T00:24:28.089439+00:00
-- url     : https://prove2.me/theorems/9bac437a-f08a-4799-b19b-f0cbb2bc93ea
-- title:
--   Cone Radial Reduction
-- statement:
--   Definitions and structural lemmas for Cone Radial Reduction, from Mathlib Initiative and contributors's pinned A real sum-product counterexample conditional on Martinet’s tower theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
namespace DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
noncomputable def radialMap (r : ℝ) (x : mixedSpace K) : mixedSpace K :=
  (r ^ ((finrank ℚ K : ℝ)⁻¹)) • x
noncomputable def radialProj (x : mixedSpace K) : mixedSpace K :=
  radialMap K (mixedEmbedding.norm x)⁻¹ x
def normEqOneSurface : Set (mixedSpace K) :=
  mixedEmbedding.fundamentalCone K ∩ {x | mixedEmbedding.norm x = 1}
variable {K}
noncomputable def surfaceMeasure (K : Type*) [Field K] [NumberField K] :
    Measure (mixedSpace K) :=
  Measure.map (radialProj K)
    ((DedekindZeta.mixedMulHaar K).restrict
      (mixedEmbedding.fundamentalCone K ∩
        {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}))
variable (K) in
/-- **The orbit-integrated radial theta** `F(𝔞, r)`.

`F(𝔞, r) = ∫_{S K} Θ(𝔞, radialMap K r σ) dμ_S σ`, the integral of
`Theta.idealThetaKernel K 𝔞` over the radius-`r` slice of the norm-1 surface
fundamental domain `normEqOneSurface K`: every `σ ∈ S K` is rescaled by
`radialMap K r` so that `mixedEmbedding.norm (radialMap K r σ) = r`
(`norm_radialMap_of_mem`). This is the one-dimensional function whose Mellin
transform is the per-class cone Mellin (`coneMellin_idealThetaKernel_eq_mellin`). -/
noncomputable def orbitTheta (𝔞 : Ideal (𝓞 K)) (r : ℝ) : ℂ :=
  ∫ σ in normEqOneSurface K, Theta.idealThetaKernel K 𝔞 (radialMap K r σ)
    ∂(surfaceMeasure K)
variable (K) in
/-- **The surface-volume constant** `V = vol(normEqOneSurface K)` (as a complex
scalar): the orbit integral of the constant `1` over the norm-1 surface
fundamental domain. This is the `+1`/zero-lattice term of the orbit-integrated
theta (the standard treatment) and the constant term `a₀` of the completed radial
theta `radialTheta`. It does not depend on the ideal `𝔞`. -/
noncomputable def surfaceVolume : ℂ :=
  ((surfaceMeasure K (normEqOneSurface K)).toReal : ℂ)
variable (K) in
/-- **Orbit-integrated radial theta of a fractional ideal** `I` (the dual case).

Like `orbitTheta`, but integrating `Theta.mixedThetaKernel K I` (the
fractional-ideal kernel) over the radius-`r` slice of the norm-1 surface, so it
applies to the dual fractional ideal `Theta.dualIdeal K 𝔞`. For integral `𝔞` it
agrees with `orbitTheta K 𝔞` via `Theta.idealThetaKernel_eq_mixed`. -/
noncomputable def orbitThetaFrac (I : FractionalIdeal (𝓞 K)⁰ K) (r : ℝ) : ℂ :=
  ∫ σ in normEqOneSurface K, Theta.mixedThetaKernel K I (radialMap K r σ)
    ∂(surfaceMeasure K)
variable (K) in
/-- **The completed radial theta** `F(𝔞, r) = orbitTheta K 𝔞 r + V` (the standard treatment's
`f(y)`): the orbit-integrated theta with the zero-lattice constant `V` restored,
so that its limit at `∞` is `a₀ = V` and it satisfies the clean inversion law
fed to `IsMellinPair`. See the section docstring for why the `+ V` is required. -/
noncomputable def radialTheta (𝔞 : Ideal (𝓞 K)) (r : ℝ) : ℂ :=
  orbitTheta K 𝔞 r + surfaceVolume K
variable (K) in
/-- **The dual completed radial theta** `G(𝔞, r) = orbitThetaFrac K (𝔞𝔡)⁻¹ r + V`
(the standard treatment's `g(y)`): the completed radial theta of the dual ideal
`Theta.dualIdeal K 𝔞`, the partner of `radialTheta K 𝔞` in the functional
equation. -/
noncomputable def radialThetaDual (𝔞 : Ideal (𝓞 K)) (r : ℝ) : ℂ :=
  orbitThetaFrac K (Theta.dualIdeal K 𝔞) r + surfaceVolume K
variable (K) in
/-- **The Minkowski quadratic form** `Q(y) = ∑_w mult w · ‖y‖_w²` on `K_ℝ`: the
exponent (up to `-π`) of `Theta.mixedGaussian`. A complex place contributes
`2|y_w|²` via `mult w = 2`. the standard treatment. -/
noncomputable def mixedQuadForm (y : mixedSpace K) : ℝ :=
  ∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) * normAtPlace w y ^ 2
end DedekindZeta.ConeRadialReduction



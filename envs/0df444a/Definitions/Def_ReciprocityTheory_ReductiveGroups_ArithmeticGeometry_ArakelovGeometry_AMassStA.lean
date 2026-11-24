-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:30.033665+00:00
-- url     : https://prove2.me/theorems/da57c903-0c3d-4415-bf53-b55751cbceb7
-- title:
--   AMass St A
-- statement:
--   Definitions and structural lemmas for AMass St A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AMassStA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open MeasureTheory Set Filter Topology
open scoped ENNReal
section FS
open ReciprocityTheory.ChartRestriction.G.Geo
variable {D : ℕ}
def gbBilL (D : ℕ) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v u => ∑ i, ((v i).re * (u i).re + (v i).im * (u i).im))
    (fun a b c => by simp only [Pi.add_apply, Complex.add_re, Complex.add_im, ← Finset.sum_add_distrib]; congr 1; ext; ring)
    (fun r a b => by simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, smul_eq_mul, Finset.mul_sum]; congr 1; ext; ring)
    (fun a b c => by simp only [Pi.add_apply, Complex.add_re, Complex.add_im, ← Finset.sum_add_distrib]; congr 1; ext; ring)
    (fun r a b => by simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, smul_eq_mul, Finset.mul_sum]; congr 1; ext; ring)
def gbBil (D : ℕ) : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((Fin D → ℂ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ gbBilL D)
def gbG (y : Fin D → ℂ) : ℝ := 1 + ∑ i, ‖y i‖ ^ 2
def gbPot (y : Fin D → ℂ) : ℝ := Real.log (Real.sqrt (1 + ∑ i, ‖y i‖ ^ 2))
end FS
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry



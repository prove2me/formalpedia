-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:35.534826+00:00
-- url     : https://prove2.me/theorems/d2012315-0320-42b8-81bc-77965c1e6d2e
-- title:
--   Hecke Phi Fourier Constant At Zero Differentiable On
-- statement:
--   Definitions and structural lemmas for Hecke Phi Fourier Constant At Zero Differentiable On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierConstantAtZeroDifferentiableOn.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
namespace GlobalTheory.HeckeTwoC
open MeasureTheory
def lg (t : ℝ) : ℝ := Real.log ‖(t : ℂ) + I‖
def G (σ : ℂ) (t : ℝ) : ℂ := ((t : ℂ) + I)⁻¹ ^ 2 * Complex.exp ((lg t : ℂ) * (-2 * σ))
def G' (σ : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) + I)⁻¹ ^ 2 * (Complex.exp ((lg t : ℂ) * (-2 * σ)) * ((lg t : ℂ) * (-2)))
end GlobalTheory.HeckeTwoC
namespace GlobalTheory.HeckeTwo
open MeasureTheory GlobalTheory.HeckeTwoC
end GlobalTheory.HeckeTwo



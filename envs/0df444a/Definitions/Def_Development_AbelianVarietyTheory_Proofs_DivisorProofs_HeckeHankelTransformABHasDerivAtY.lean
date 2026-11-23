-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:52:09.997805+00:00
-- url     : https://prove2.me/theorems/4fbfe068-842b-4e44-836a-85e92be5e293
-- title:
--   Hecke Hankel Transform ABHas Deriv At Y
-- statement:
--   Definitions and structural lemmas for Hecke Hankel Transform ABHas Deriv At Y, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABHasDerivAtY.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
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
namespace GlobalTheory.HeckeTwoDY
open MeasureTheory
def wt (t y : ℝ) : ℂ := (t : ℂ) + (y : ℂ) * I
def igE (a b : ℕ) (σ : ℂ) (ν y t : ℝ) : ℂ :=
  (wt t y)⁻¹ ^ a * ((starRingEnd ℂ) (wt t y))⁻¹ ^ b *
    Complex.exp ((Real.log (t ^ 2 + y ^ 2) : ℂ) * (-σ)) * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))
end GlobalTheory.HeckeTwoDY
noncomputable section
namespace GlobalTheory.HeckeTwoDY
open MeasureTheory
end GlobalTheory.HeckeTwoDY
noncomputable section
namespace GlobalTheory.HeckeTwoDY
open MeasureTheory
end GlobalTheory.HeckeTwoDY
namespace GlobalTheory.HeckeTwo
open MeasureTheory GlobalTheory.HeckeTwoDY
end GlobalTheory.HeckeTwo



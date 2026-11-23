-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigma
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigma
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:52.623655+00:00
-- url     : https://prove2.me/theorems/344efa12-dc32-4587-90a2-7d0b0e7f3369
-- title:
--   Hecke Hankel Transform ABDifferentiable On Sigma
-- statement:
--   Definitions and structural lemmas for Hecke Hankel Transform ABDifferentiable On Sigma, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABDifferentiableOnSigma.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
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
namespace GlobalTheory.HeckeTwoAB
open MeasureTheory GlobalTheory.HeckeTwoC
def wt (y t : ℝ) : ℂ := (t : ℂ) + (y : ℂ) * I
def L (y t : ℝ) : ℝ := Real.log |y| + lg (t / y)
def F (a b : ℕ) (ν y : ℝ) (σ : ℂ) (t : ℝ) : ℂ :=
  (wt y t)⁻¹ ^ a * ((starRingEnd ℂ) (wt y t))⁻¹ ^ b * Complex.exp ((L y t : ℂ) * (-2 * σ)) *
    Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))
def F' (a b : ℕ) (ν y : ℝ) (σ : ℂ) (t : ℝ) : ℂ :=
  (wt y t)⁻¹ ^ a * ((starRingEnd ℂ) (wt y t))⁻¹ ^ b *
    (Complex.exp ((L y t : ℂ) * (-2 * σ)) * ((L y t : ℂ) * (-2))) *
    Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))
end GlobalTheory.HeckeTwoAB
namespace GlobalTheory.HeckeTwo
open MeasureTheory GlobalTheory.HeckeTwoC GlobalTheory.HeckeTwoAB
end GlobalTheory.HeckeTwo



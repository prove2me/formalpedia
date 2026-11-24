-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormMulNormalisedAbsPowHalfEqOne
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormMulNormalisedAbsPowHalfEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:38.607899+00:00
-- url     : https://prove2.me/theorems/148a4f40-cf91-4562-98c8-59d6a78bda90
-- title:
--   Norm Mul Normalised Abs Pow Half Eq One
-- statement:
--   Definitions and structural lemmas for Norm Mul Normalised Abs Pow Half Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormMulNormalisedAbsPowHalfEqOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SplitFlip_apow_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero


set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
noncomputable section
namespace GlobalTheory.CharNormHalf
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def normTwist (d : ℕ) (χ : kˣ →* ℂˣ) : kˣ →* ℂˣ where
  toFun x := Units.mk0 (((‖(χ x : ℂ)‖ : ℝ) : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2)))
    (mul_ne_zero (by exact_mod_cast (norm_ne_zero_iff.2 (χ x).ne_zero)) (GlobalTheory.SplitFlip.apow_ne_zero _ _))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [map_mul, Units.val_mul, norm_mul, Complex.ofReal_mul, Units.val_mk0, GlobalTheory.SplitFlip.apow_mul]
    ring
end GlobalTheory.CharNormHalf



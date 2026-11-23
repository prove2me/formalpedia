-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClassesSelfDualOfSelfDual
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClassesSelfDualOfSelfDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:16.875267+00:00
-- url     : https://prove2.me/theorems/16b3b9c6-81d3-4142-b7e9-c7fa1eb166d4
-- title:
--   Finite Classes Self Dual Of Self Dual
-- statement:
--   Definitions and structural lemmas for Finite Classes Self Dual Of Self Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FiniteClassesSelfDualOfSelfDual.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Theorems.Thm_GlobalTheory_DualFamily_herm_one_eq
import Theorems.Thm_GlobalTheory_TraceDualMin_herm_one_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
namespace GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace SelfDualClasses
open ShortVectors
noncomputable def hermRat (n : ℕ) : (Fin n → E) →ₗ[ℚ] (Fin n → E) →ₗ[ℚ] E :=
  LinearMap.mk₂ ℚ (fun x y => herm 1 x y)
    (fun x x' y => by simp [DualFamily.herm_one_eq, add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [DualFamily.herm_one_eq, Finset.smul_sum])
    (fun x y y' => by simp [DualFamily.herm_one_eq, cc, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp [DualFamily.herm_one_eq, Finset.smul_sum, cc, Rat.smul_def, mul_left_comm])
end SelfDualClasses
end GlobalTheory



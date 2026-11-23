-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:09.45555+00:00
-- url     : https://prove2.me/theorems/06e33da7-dd2b-4820-9bd7-2f44099d7dbf
-- title:
--   Trace Herm Nondegenerate
-- statement:
--   Definitions and structural lemmas for Trace Herm Nondegenerate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TraceHermNondegenerate.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
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
namespace ShortVectors
section Rational
variable {V : Type} [AddCommGroup V] [Module ℚ V]
end Rational
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
noncomputable def traceHerm (n : ℕ) : LinearMap.BilinForm ℚ (Fin n → E) :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ E (herm 1 x y))
    (fun x x' y => by simp [DualFamily.herm_one_eq, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      rw [← map_smul]; congr 1; simp [DualFamily.herm_one_eq, Finset.smul_sum])
    (fun x y y' => by simp [DualFamily.herm_one_eq, cc, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      rw [← map_smul]; congr 1
      simp [DualFamily.herm_one_eq, Finset.smul_sum, cc, Rat.smul_def, mul_left_comm])
end ShortVectors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory



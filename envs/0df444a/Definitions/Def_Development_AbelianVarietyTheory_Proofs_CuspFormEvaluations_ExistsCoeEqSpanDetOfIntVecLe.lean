-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T16:52:57.774123+00:00
-- url     : https://prove2.me/theorems/9db2c929-ae27-5e74-ae29-2d21d7212b44
-- title:
--   Exists Coe Eq Span Det Of Int Vec Le
-- statement:
--   Definitions and structural lemmas for Exists Coe Eq Span Det Of Int Vec Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsCoeEqSpanDetOfIntVecLe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_DualLattices_WedgeNeZeroOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
open scoped nonZeroDivisors
section Period
variable {E : Type} [Field E] [NumberField E]
end Period
section Index
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
end Index
section Modulus
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable [IsGalois ℚ E]
variable {K : Type*} [Field K] [Algebra E K]
end Modulus
section IndexIdeal
open ReciprocityTheory.MultiplicativeHeights.SemiDegIdx ReciprocityTheory.PGsh
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
attribute [local instance] extModR
end IndexIdeal
section Main
open ReciprocityTheory.PGsh
attribute [local instance] extModR
end Main
end GlobalTheory.TensorLat



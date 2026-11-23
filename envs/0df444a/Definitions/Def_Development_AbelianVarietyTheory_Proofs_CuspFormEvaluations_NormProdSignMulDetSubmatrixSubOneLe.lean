-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormProdSignMulDetSubmatrixSubOneLe
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormProdSignMulDetSubmatrixSubOneLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:37:30.107802+00:00
-- url     : https://prove2.me/theorems/c5f74acf-daa4-4f5b-a1c1-713c64ef11fb
-- title:
--   Norm Prod Sign Mul Det Submatrix Sub One Le
-- statement:
--   Definitions and structural lemmas for Norm Prod Sign Mul Det Submatrix Sub One Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_ScaledBoundInequality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram
namespace GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory



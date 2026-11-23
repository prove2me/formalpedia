-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:24.184827+00:00
-- url     : https://prove2.me/theorems/75c541a6-c65a-41be-b048-c7300c55740c
-- title:
--   Finrank Mul Discr Rpow Le Sum Sq Of Mem Trace Dual
-- statement:
--   Definitions and structural lemmas for Finrank Mul Discr Rpow Le Sum Sq Of Mem Trace Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
namespace GlobalTheory
section General
variable {K : Type*} [Field K] [NumberField K]
end General
section TotallyReal
variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
end TotallyReal
end GlobalTheory



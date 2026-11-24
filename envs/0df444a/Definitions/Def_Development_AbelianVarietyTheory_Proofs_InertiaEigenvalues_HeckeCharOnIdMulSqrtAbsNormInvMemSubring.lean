-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HeckeCharOnIdMulSqrtAbsNormInvMemSubring
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HeckeCharOnIdMulSqrtAbsNormInvMemSubring
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:33.368796+00:00
-- url     : https://prove2.me/theorems/6cc5d7ec-89a3-448a-8b8f-e925464fa741
-- title:
--   Hecke Char On Id Mul Sqrt Abs Norm Inv Mem Subring
-- statement:
--   Definitions and structural lemmas for Hecke Char On Id Mul Sqrt Abs Norm Inv Mem Subring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeCharOnIdMulSqrtAbsNormInvMemSubring.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open scoped nonZeroDivisors
namespace GlobalTheory.HeckeIdealValue
open Formalism.L2.Host
variable {L : Type} [Field L] [NumberField L]
end GlobalTheory.HeckeIdealValue



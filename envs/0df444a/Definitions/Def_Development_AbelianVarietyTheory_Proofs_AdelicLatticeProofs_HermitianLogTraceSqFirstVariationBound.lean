-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HermitianLogTraceSqFirstVariationBound
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HermitianLogTraceSqFirstVariationBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:07.282633+00:00
-- url     : https://prove2.me/theorems/205f453d-fd73-443a-87ce-620925368330
-- title:
--   Hermitian Log Trace Sq First Variation Bound
-- statement:
--   Definitions and structural lemmas for Hermitian Log Trace Sq First Variation Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HermitianLogTraceSqFirstVariationBound.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LogSqLeTangentAddSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
namespace GlobalTheory.ClassFin.LogSqVar
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end GlobalTheory.ClassFin.LogSqVar



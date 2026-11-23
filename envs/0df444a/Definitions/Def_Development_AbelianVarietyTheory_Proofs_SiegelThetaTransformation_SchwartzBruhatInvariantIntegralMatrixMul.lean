-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:44.010308+00:00
-- url     : https://prove2.me/theorems/1435de83-9695-4ae9-b34a-ed06d3c98a51
-- title:
--   Schwartz Bruhat Invariant Integral Matrix Mul
-- statement:
--   Definitions and structural lemmas for Schwartz Bruhat Invariant Integral Matrix Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
namespace GlobalTheory.SW.LinChange
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
end GlobalTheory.SW.LinChange



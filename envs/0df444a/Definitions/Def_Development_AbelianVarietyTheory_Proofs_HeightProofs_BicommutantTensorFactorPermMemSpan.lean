-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BicommutantTensorFactorPermMemSpan
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_BicommutantTensorFactorPermMemSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:58:02.610808+00:00
-- url     : https://prove2.me/theorems/8a1852fd-55af-4d37-9765-b3948fdd9e54
-- title:
--   Bicommutant Tensor Factor Perm Mem Span
-- statement:
--   Definitions and structural lemmas for Bicommutant Tensor Factor Perm Mem Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BicommutantTensorFactorPermMemSpan.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
namespace GlobalTheory.SmoothForms
end GlobalTheory.SmoothForms



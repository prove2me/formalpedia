-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DeformedProductDerivativeTermNormLeUniform
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DeformedProductDerivativeTermNormLeUniform
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:53:16.843526+00:00
-- url     : https://prove2.me/theorems/14cf8244-7d93-47d0-9eb6-2f3f60f3ff73
-- title:
--   Deformed Product Derivative Term Norm Le Uniform
-- statement:
--   Definitions and structural lemmas for Deformed Product Derivative Term Norm Le Uniform, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DeformedProductDerivativeTermNormLeUniform.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
namespace GlobalTheory.DeformedSum.Bound
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
end GlobalTheory.DeformedSum.Bound



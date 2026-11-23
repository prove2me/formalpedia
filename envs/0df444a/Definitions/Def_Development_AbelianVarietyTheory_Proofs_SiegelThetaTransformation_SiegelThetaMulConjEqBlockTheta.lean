-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaMulConjEqBlockTheta
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaMulConjEqBlockTheta
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:10.967088+00:00
-- url     : https://prove2.me/theorems/2f76a140-fdc5-4b40-b02f-217fa311112f
-- title:
--   Siegel Theta Mul Conj Eq Block Theta
-- statement:
--   Definitions and structural lemmas for Siegel Theta Mul Conj Eq Block Theta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaMulConjEqBlockTheta.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
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
namespace GlobalTheory.SW.ThetaProd
def colsEquiv (κ ι₁ ι₂ : Type) : Matrix κ (ι₁ ⊕ ι₂) ℚ ≃ Matrix κ ι₁ ℚ × Matrix κ ι₂ ℚ where
  toFun m := (m.toCols₁, -m.toCols₂)
  invFun p := fromCols p.1 (-p.2)
  left_inv m := by simp
  right_inv p := by simp
end GlobalTheory.SW.ThetaProd



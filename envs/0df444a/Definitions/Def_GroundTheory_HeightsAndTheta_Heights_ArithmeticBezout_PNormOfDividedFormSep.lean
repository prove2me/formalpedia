-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PNormOfDividedFormSep
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PNormOfDividedFormSep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:26.899655+00:00
-- url     : https://prove2.me/theorems/ae7e2960-4c50-452e-8d05-5a4bdc1df102
-- title:
--   PNorm Of Divided Form Sep
-- statement:
--   Definitions and structural lemmas for PNorm Of Divided Form Sep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PNormOfDividedFormSep.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormSep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
open scoped nonZeroDivisors
noncomputable section
namespace NormOfDividedFormSep
variable {O B K L : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B] [Field K] [Field L] [Algebra O K]
  [IsFractionRing O K] [Algebra B L] [Algebra K L] [Algebra O L] [IsScalarTower O K L] [IsScalarTower O B L]
  [IsLocalization (Algebra.algebraMapSubmonoid B O⁰) L]
end NormOfDividedFormSep
end
end GroundTheory.Heights₂.Heights



-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntAfApproxInterUnitConj
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntAfApproxInterUnitConj
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:39:30.522509+00:00
-- url     : https://prove2.me/theorems/039e6ff6-7492-401a-b6dc-a2d2bb10cb0b
-- title:
--   Int Af Approx Inter Unit Conj
-- statement:
--   Definitions and structural lemmas for Int Af Approx Inter Unit Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntAfApproxInterUnitConj.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
namespace GlobalTheory.RowLev
end GlobalTheory.RowLev



-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryCarryDual
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryCarryDual
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-27T05:34:23.101058+00:00
-- url     : https://prove2.me/theorems/ede504b3-42ae-49de-8694-5d1afa48381a
-- title:
--   Unitary Carry Dual
-- statement:
--   Definitions and structural lemmas for Unitary Carry Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UnitaryCarryDual.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.Mem.LevDual
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
end GlobalTheory.Mem.LevDual
namespace GlobalTheory.Mem.LevDual
end GlobalTheory.Mem.LevDual



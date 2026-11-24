-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UniformizerPowerTorusMemNormalUnitarySubgroup
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_UniformizerPowerTorusMemNormalUnitarySubgroup
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:48:11.954292+00:00
-- url     : https://prove2.me/theorems/1e594219-0e05-4c93-bbe9-3b40a0db854a
-- title:
--   Uniformizer Power Torus Mem Normal Unitary Subgroup
-- statement:
--   Definitions and structural lemmas for Uniformizer Power Torus Mem Normal Unitary Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UniformizerPowerTorusMemNormalUnitarySubgroup.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
namespace GlobalTheory.TorusNormal
open Formalism.UG.P
variable {L : Type} [Field L]
def pm {n : ℕ} (f g : Fin n → L) : Matrix (Fin n) (Fin n) L :=
  Matrix.of fun i j => (if j = i then f i else 0) + (if j = Fin.rev i then g i else 0)
end GlobalTheory.TorusNormal
namespace GlobalTheory.TorusNormal
open Formalism.UG.P
variable {L : Type} [Field L]
end GlobalTheory.TorusNormal
namespace GlobalTheory.TorusNormal
open Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
end GlobalTheory.TorusNormal
namespace GlobalTheory
open Formalism.UG.P GlobalTheory.TorusNormal
end GlobalTheory



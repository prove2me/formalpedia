-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZRows
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZRows
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:57:16.007883+00:00
-- url     : https://prove2.me/theorems/f5da6b68-61b3-4b8d-8f08-fc24396c77a4
-- title:
--   PVery Ample ZRows
-- statement:
--   Definitions and structural lemmas for PVery Ample ZRows, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZRows.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZRowsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechPartitionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartSmulSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartLocalSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v w
namespace VeryAmpleZRows
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] {n : ℕ} {U : Finset (Fin n)}
def onSet {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (A : Finset (Fin n)) : V :=
  if h : A.card = i + 1 ∧ A ⊆ U then s ⟨⟨A, Finset.card_pos.mp (by omega), h.2⟩, h.1⟩ else 0
end VeryAmpleZRows
end
end GroundTheory.Heights₂.Heights.Kleiman



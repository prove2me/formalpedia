-- Prove2me | Definitions.Def_RequestProject_ElevenTwelfths
-- name    : RequestProject_ElevenTwelfths
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:13:27.955963+00:00
-- url     : https://prove2.me/theorems/7b52ede5-420c-44ae-b4e4-0de61516c2fa
-- title:
--   Eleven Twelfths
-- statement:
--   Definitions and structural lemmas for Eleven Twelfths, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ElevenTwelfths.lean

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_FeigeNorkin
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace ElevenTwelfths
open FeigeNorkin
noncomputable def instV : Fin 3 → Fin 8 → ℝ :=
  ![fun g => (fnR g : ℝ), fun g => (fnC g : ℝ), fun _ => 0]
noncomputable def instP (δ : ℝ) : Fin 8 → ℝ := fun g => δ * (fnU g : ℝ)
end ElevenTwelfths
end FairSelling



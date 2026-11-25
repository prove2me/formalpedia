-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_FWNatural
-- name    : GroundTheory_PAdicHodge_FWNatural
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T11:40:12.557098+00:00
-- url     : https://prove2.me/theorems/9c4e985d-0567-4a1d-bf70-2817617c751f
-- title:
--   FWNatural
-- statement:
--   Definitions and structural lemmas for FWNatural, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWNatural.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
local notation "θ" => WittVector.fontaineTheta (normInteger C) p
end GroundTheory.PAdicHodge



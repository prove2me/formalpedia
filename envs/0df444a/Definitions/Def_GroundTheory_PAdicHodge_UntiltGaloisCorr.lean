-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
-- name    : GroundTheory_PAdicHodge_UntiltGaloisCorr
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T10:01:12.53398+00:00
-- url     : https://prove2.me/theorems/5ef583b2-80c6-4935-95de-984f154ca91f
-- title:
--   Untilt Galois Corr
-- statement:
--   Definitions and structural lemmas for Untilt Galois Corr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGaloisCorr.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
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
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
section Injective
end Injective
section Galois
end Galois
section Theta
end Theta
section Correspondence
end Correspondence
end GroundTheory.PAdicHodge



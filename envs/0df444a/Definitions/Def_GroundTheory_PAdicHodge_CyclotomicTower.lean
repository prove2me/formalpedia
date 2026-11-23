-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
-- name    : GroundTheory_PAdicHodge_CyclotomicTower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:31.890906+00:00
-- url     : https://prove2.me/theorems/ee7fd034-e76c-4d78-af3c-eeac9fc23c33
-- title:
--   Cyclotomic Tower
-- statement:
--   Definitions and structural lemmas for Cyclotomic Tower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Theorems.Thm_GroundTheory_PAdicHodge_exists_isPrimitiveRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable (p) in

def cyclRadius (j : ℕ) : ℝ := ‖(exists_isPrimitiveRoot (p := p) j).choose - 1‖
def cyclCoord (k : ℕ) (η y : PadicAlgCl p) (i : ℕ) : PadicAlgCl p :=
  normTrace (cycl p k) (y * η ^ (p ^ (k + 1) - i))
end
end GroundTheory.PAdicHodge



-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_FWCyclotomicNorm
-- name    : GroundTheory_PAdicHodge_FWCyclotomicNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:21.258972+00:00
-- url     : https://prove2.me/theorems/a9bb7345-dfeb-4d54-a831-2afc4a5bc69f
-- title:
--   FWCyclotomic Norm
-- statement:
--   Definitions and structural lemmas for FWCyclotomic Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCyclotomicNorm.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
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
open IntermediateField Polynomial
section Ultra
variable {R : Type*} [NormedField R] [IsUltrametricDist R]
end Ultra
variable {p : ℕ} [Fact p.Prime]
section Ortho
variable {k : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
include hζ
end Ortho
end GroundTheory.PAdicHodge



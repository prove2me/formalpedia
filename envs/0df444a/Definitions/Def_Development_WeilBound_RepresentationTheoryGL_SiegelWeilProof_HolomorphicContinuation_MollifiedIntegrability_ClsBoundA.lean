-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:35.402852+00:00
-- url     : https://prove2.me/theorems/449d3a21-cc17-494b-9e7a-ea6d00d72bcb
-- title:
--   Cls Bound A
-- statement:
--   Definitions and structural lemmas for Cls Bound A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundA.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
namespace PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
def Am (s : ℂ) (y : E n) : Matrix (Fin n) (Fin n) ℂ := 1 - (Complex.I * s) • herm y
def Bm (s : ℂ) (y : E n) : Matrix (Fin n) (Fin n) ℂ := 1 + (Complex.I * s) • herm y
end PositivityTheory.Rg.Sw.WR.B



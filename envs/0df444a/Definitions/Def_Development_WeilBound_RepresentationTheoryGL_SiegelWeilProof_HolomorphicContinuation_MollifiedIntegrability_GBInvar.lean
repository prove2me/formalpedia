-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:20.001213+00:00
-- url     : https://prove2.me/theorems/92c70f5c-1603-4136-a401-e3fd536060d2
-- title:
--   GBInvar
-- statement:
--   Definitions and structural lemmas for GBInvar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBInvar.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
namespace PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace Inv
def E (p : Fin n × Fin n) : Mc n := Matrix.single p.1 p.2 1
def dd (H : Mc n) (F : Mc n → ℂ) : Mc n → ℂ := fun b => fderiv ℂ F b H
def wd (L : List (Mc n)) (F : Mc n → ℂ) : Mc n → ℂ := L.foldr (fun H g => dd H g) F
end Inv
end PositivityTheory.Rg.Sw.WR.K.GB



-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollId
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollId
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:30.260208+00:00
-- url     : https://prove2.me/theorems/452b4179-2f06-4013-9db6-6fc179463280
-- title:
--   Moll Id
-- statement:
--   Definitions and structural lemmas for Moll Id, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/MollId.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollIdA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ}
def gam (ε : ℝ) (y : E n) : ℂ := Complex.exp (-((ε * ip y y : ℝ) : ℂ))
def kr (ε t : ℝ) (u : E n) : ℂ := ∫ y, gam ε y * Complex.exp (Complex.I * t * ip y u)
def mM (ψ : E n → ℂ) (l : ℝ) (w : E n) : ℂ := ∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ)
end PositivityTheory.Rg.Sw.WR.D.Moll



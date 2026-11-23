-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:35.476801+00:00
-- url     : https://prove2.me/theorems/33517e18-dbe9-41a8-9384-4ff54ae3ef3c
-- title:
--   Integrable Of Bound
-- statement:
--   Definitions and structural lemmas for Integrable Of Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean

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
open MeasureTheory Matrix
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.WR.Ib
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {n : ℕ}
def lf (t : ℝ) (β : E n) : E n →L[ℝ] ℂ :=
  ∑ a, ∑ b, (-(Complex.I * t * β a b)) • (Complex.ofRealCLM.comp
    ((ContinuousLinearMap.proj b : (Fin n → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj a : E n →L[ℝ] (Fin n → ℝ))))
end PositivityTheory.Rg.Sw.WR.Ib
namespace PositivityTheory.Rg.Sw.WR
end PositivityTheory.Rg.Sw.WR



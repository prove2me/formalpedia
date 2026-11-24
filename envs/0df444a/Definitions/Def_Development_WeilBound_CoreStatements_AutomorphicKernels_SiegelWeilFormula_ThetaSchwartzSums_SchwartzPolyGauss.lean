-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSchwartzSums_SchwartzPolyGauss
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSchwartzSums_SchwartzPolyGauss
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:43.007081+00:00
-- url     : https://prove2.me/theorems/54a90981-ed8a-49e1-81eb-5fc5620dfcf0
-- title:
--   Schwartz Poly Gauss
-- statement:
--   Definitions and structural lemmas for Schwartz Poly Gauss, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSchwartzSums/SchwartzPolyGauss.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap
namespace PositivityTheory.SiegelWeilFormula.KMain
open PositivityTheory.Rg.Sw
def coordX {m n : ℕ} (k : Fin m × Fin n × Bool) (x : Fin m → Fin n → ℂ) : ℂ :=
  if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1
end PositivityTheory.SiegelWeilFormula.KMain
end



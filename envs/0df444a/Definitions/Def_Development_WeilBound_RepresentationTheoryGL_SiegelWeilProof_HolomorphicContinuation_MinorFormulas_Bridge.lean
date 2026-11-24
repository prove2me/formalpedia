-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_Bridge
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_Bridge
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:30.877805+00:00
-- url     : https://prove2.me/theorems/e92f5178-23ab-4fe3-835c-bcbe36d419f1
-- title:
--   Bridge
-- statement:
--   Definitions and structural lemmas for Bridge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/Bridge.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
def opsSeq (s : ℂ) (m : ℕ) : (k : ℕ) → (Fin k → Fin n × Fin n) → Fm n → Fm n
  | 0, _, Q => Q
  | k + 1, dirs, Q => opD s m (dirs 0).1 (dirs 0).2 (opsSeq s m k (Fin.tail dirs) Q)
end PositivityTheory.Rg.Sw.SP



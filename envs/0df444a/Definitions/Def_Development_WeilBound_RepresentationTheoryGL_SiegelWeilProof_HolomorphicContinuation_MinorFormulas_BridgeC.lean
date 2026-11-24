-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeC
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:38:48.76333+00:00
-- url     : https://prove2.me/theorems/4d10f131-52e9-4666-bace-4097c23d2f79
-- title:
--   Bridge C
-- statement:
--   Definitions and structural lemmas for Bridge C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeC.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeB
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
namespace PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
def gD (s : ℂ) (x : MC n) (k l : Fin n) (kk : Bool × Fin n × Fin n) : ℂ :=
  if kk.1 then (-(Complex.I * s) • (Yp s x * Matrix.of (eU k l) * Yp s x)) kk.2.1 kk.2.2
  else ((Complex.I * s) • (Ym s x * Matrix.of (eU k l) * Ym s x)) kk.2.1 kk.2.2
end PositivityTheory.Rg.Sw.SP



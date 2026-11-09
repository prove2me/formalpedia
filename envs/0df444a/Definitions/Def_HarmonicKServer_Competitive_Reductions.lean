-- Prove2me | Definitions.Def_HarmonicKServer_Competitive_Reductions
-- name    : HarmonicKServer_Competitive_Reductions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:24.554109+00:00
-- url     : https://prove2.me/theorems/7a527cfd-2d50-48c9-aa86-3b29ab4e9f72
-- title:
--   §2 footnote 2 — Private-edge extension distances
-- statement:
--   Attach a private edge of length $\varepsilon>0$ to each initial adversary label $i$, rooted at $y_i$. The extension has points $V\sqcup[k]$. Old distances remain unchanged; a new endpoint $i$ is at distance $\varepsilon+d(y_i,v)$ from an old point $v$, and different new endpoints have distance $2\varepsilon+d(y_i,y_j)$:
--   $$d_\varepsilon(i,j)=2\varepsilon+d(y_i,y_j)\quad(i\ne j).$$
--   A point has distance zero from itself. This is a concrete distance formula, including collocated original roots. The separate private-edge theorem must construct its metric instance and lift causal schedules with the fixed extra cost $k\varepsilon$.
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 3, §2 footnote 2 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Mathlib
import Definitions.Def_HarmonicKServer_Competitive_Harmonic

namespace HarmonicKServer.Competitive

/-- Distances in the original metric with one private epsilon edge at each labelled start. -/
noncomputable def privateDistance {k : ℕ} {V : Type*} [MetricSpace V]
    (Y : KServer.Config k V) (ε : ℝ) : V ⊕ Fin k → V ⊕ Fin k → ℝ
  | .inl v, .inl w => dist v w
  | .inr i, .inl v => ε + dist (Y i) v
  | .inl v, .inr i => dist v (Y i) + ε
  | .inr i, .inr j => if i = j then 0 else 2 * ε + dist (Y i) (Y j)

end HarmonicKServer.Competitive



-- Prove2me | Definitions.Def_IPMJumpLB_pathGap
-- name    : IPMJumpLB_pathGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:22.741018+00:00
-- url     : https://prove2.me/theorems/7a75a793-8d83-44eb-80af-61f11aac3c5c
-- title:
--   Path-arc gap term $D_P$
-- statement:
--   For a potential $x$ (slacks $s = c - Bx$) and a flow $f$ on the Section 4 instance,
--   $$
--   D_P = \sum_{i=0}^{k-1} \bigl(s_{e_i^+} f_{e_i^+} + s_{e_i^-} f_{e_i^-}\bigr),
--   $$
--   the contribution of the $2k$ path arcs to the duality gap.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), Section 3.1, p.6, reused in the proof of Theorem 4.1, p.11

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance
import Definitions.Def_IPMJumpLB_slack
import Definitions.Def_IPMJumpLB_VertexU
import Definitions.Def_IPMJumpLB_ArcU
import Definitions.Def_IPMJumpLB_nHat
import Definitions.Def_IPMJumpLB_unitSSSP

namespace IPMJumpLB

/-- `D_P = ∑_(i=0)^(k−1) (s_(e⁺ᵢ) f_(e⁺ᵢ) + s_(e⁻ᵢ) f_(e⁻ᵢ))`, the contribution of the path arcs to
the duality gap of the Section 4 instance (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), §3.1, p.6, reused in the proof of Theorem 4.1,
p.11). -/
noncomputable def pathGap (b k : ℕ) (x : VertexU b k → ℝ) (f : ArcU b k → ℝ) : ℝ :=
  ∑ i : Fin k, (slack (unitSSSP b k) x (.fwd i) * f (.fwd i) +
    slack (unitSSSP b k) x (.bwd i) * f (.bwd i))

end IPMJumpLB



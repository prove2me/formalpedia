-- Prove2me | Definitions.Def_IPMJumpLB_shortcutOutFlow
-- name    : IPMJumpLB_shortcutOutFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:59.14012+00:00
-- url     : https://prove2.me/theorems/889725a7-9df8-4df4-a0de-4423f485f972
-- title:
--   Total second-shortcut-arc flow $F_{S,\mathrm{out}}$
-- statement:
--   For a flow $f$ on the Section 4 instance, the total flow on the second shortcut arcs is
--   $$
--   F_{S,\mathrm{out}}(f) = \sum_{j=1}^{(b-2)k^2} f_{(a_j, v_k)} .
--   $$
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), proof of Theorem 4.1, p.11

import Mathlib
import Definitions.Def_IPMJumpLB_ArcU

namespace IPMJumpLB

/-- `F_S,out(f) = ∑_j f_(a_j, v_k)`, the total flow on the second shortcut arcs of the Section 4
instance (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), proof of Theorem 4.1, p.11). -/
noncomputable def shortcutOutFlow (b k : ℕ) (f : ArcU b k → ℝ) : ℝ :=
  ∑ j : Fin ((b - 2) * k ^ 2), f (.scOut j)

end IPMJumpLB



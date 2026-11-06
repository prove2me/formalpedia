-- Prove2me | Definitions.Def_IPMJumpLB_shortcutInFlow
-- name    : IPMJumpLB_shortcutInFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:02.738802+00:00
-- url     : https://prove2.me/theorems/db313a76-2cff-45e3-a52f-e5075810726c
-- title:
--   Total first-shortcut-arc flow $F_{S,\mathrm{in}}$
-- statement:
--   For a flow $f$ on the Section 4 instance, the total flow on the first shortcut arcs is
--   $$
--   F_{S,\mathrm{in}}(f) = \sum_{j=1}^{(b-2)k^2} f_{(v_0, a_j)} .
--   $$
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), proof of Theorem 4.1, p.11

import Mathlib
import Definitions.Def_IPMJumpLB_ArcU

namespace IPMJumpLB

/-- `F_S,in(f) = ∑_j f_(v₀, a_j)`, the total flow on the first shortcut arcs of the Section 4
instance (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), proof of Theorem 4.1, p.11). -/
noncomputable def shortcutInFlow (b k : ℕ) (f : ArcU b k → ℝ) : ℝ :=
  ∑ j : Fin ((b - 2) * k ^ 2), f (.scIn j)

end IPMJumpLB



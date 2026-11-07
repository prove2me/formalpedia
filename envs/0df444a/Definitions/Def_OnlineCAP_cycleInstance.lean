-- Prove2me | Definitions.Def_OnlineCAP_cycleInstance
-- name    : OnlineCAP_cycleInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:28:05.155251+00:00
-- url     : https://prove2.me/theorems/e6761ff4-7cd4-4475-b33b-feea21008960
-- title:
--   OWCycAP with cut arrivals
-- statement:
--   **OWCycAP** (and, with unit costs, **OCycAP**) is the special case of OWCAP with cut arrivals in which the base graph is the cycle $v_0v_1\cdots v_{n-1}v_0$ and $k=2$: the requests are the 2-cuts of the cycle, i.e. its arcs.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Problem 2.2, p.9

import Mathlib
import Definitions.Def_OnlineCAP_crosses
import Definitions.Def_OnlineCAP_edgeCut
import Definitions.Def_OnlineCAP_IsKCut
import Definitions.Def_OnlineCAP_OnlineHSInstance
import Definitions.Def_OnlineCAP_capInstance
import Definitions.Def_OnlineCAP_cycleEnds

namespace OnlineCAP

/-- **OWCycAP with cut arrivals.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Problem 2.2, p.9 (PDF p.9): "This is the special case of
OWCAP (or OCAP) with cut arrivals in which the given base graph G is a cycle and k = 2."

The instance of `capInstance` on the standard cycle `cycleEnds n` with `k = 2`. -/
def cycleInstance (n : ℕ) (L : Finset (Sym2 (Fin n))) (c : Sym2 (Fin n) → ℝ) :
    OnlineHSInstance (Sym2 (Fin n)) (Finset (Fin n)) :=
  capInstance (cycleEnds n) 2 L c

end OnlineCAP



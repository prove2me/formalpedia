-- Prove2me | Definitions.Def_TightClock_a
-- name    : TightClock_a
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:38:31.775633+00:00
-- url     : https://prove2.me/theorems/894bc1b8-6c26-435c-bbc1-9c6edc4640d7
-- title:
--   Parameter $a=1/q$, (6.1)
-- statement:
--   The parameter $a:=1/q$ of (6.1), for an integer $q\ge 8$. Each child of a node keeps each member of the node with probability $a$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.35 (PDF p.38), eq. (6.1)

import Mathlib

set_option autoImplicit false

namespace TightClock

/-- The thinning probability `a := 1/q` of (6.1). Afshinmehr et al., manuscript (STOC 2027 submission),
§6.2, p.35 (PDF 38). -/
noncomputable def a (q : ℕ) : ℝ := 1 / (q : ℝ)

end TightClock



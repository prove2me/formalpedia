-- Prove2me | Definitions.Def_FastMinority_goodPlus
-- name    : FastMinority_goodPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:36.03083+00:00
-- url     : https://prove2.me/theorems/1617b34a-baa8-4b81-998d-d3a23f6c9fbe
-- title:
--   $\mathcal H^+=\mathcal H\cup\{0\}$
-- statement:
--   The set $\mathcal H^+=\mathcal H\cup\{0\}$ consists of the good states (3.1) together with the consensus state $0$. It is the set the analysis waits for: the time to reach it is bounded first, and then each visit gives a constant chance of consensus.
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Section 3, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_FastMinority_goodSet

set_option autoImplicit false

open Classical

namespace FastMinority

/-- `H⁺ = H ∪ {0}` (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), §3, p.6 = PDF p.8): the good states together with the consensus
state `0`. -/
def goodPlus (n k : ℕ) (b : ℝ) : Set (Fin (n + 1)) :=
  insert 0 (goodSet n k b)

end FastMinority



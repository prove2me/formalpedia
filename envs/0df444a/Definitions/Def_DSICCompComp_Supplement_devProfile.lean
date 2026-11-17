-- Prove2me | Definitions.Def_DSICCompComp_Supplement_devProfile
-- name    : DSICCompComp_Supplement_devProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:24:36.480185+00:00
-- url     : https://prove2.me/theorems/28888ac4-4d7d-443b-88d9-82a75238011e
-- title:
--   The deviation profile $(v'_i, v_{-i})$
-- statement:
--   For a value profile $v \in \mathrm{supp}(D)$, a bidder $i$ and a report $v'_i \in \mathrm{supp}(D_i) \cup \{\varnothing\}$, the profile $(v'_i, v_{-i})$ is the report profile in which bidder $i$ reports $v'_i$ and every other bidder $k$ reports $v_k$. With $v'_i = v_i$ it is the truthful profile $v$.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Appendix C, p.35 (pdf p.36)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_FiniteSetting

namespace DSICCompComp

namespace Supplement

/-- The report profile `(v'_i, v_{-i})` in which bidder `i` reports `v'_i ∈ supp(D_i) ∪ {∅}` and every
other bidder `k` reports her value `v_k` (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Appendix C, p.35 (pdf p.36)).

**Formalization Note** `w = none` is `∅`; `devProfile E v i (some (v i))` is the truthful profile
`fun k => some (v k)`. -/
def devProfile {n m : ℕ} (E : FiniteSetting n m) (v : (i : Fin n) → E.S i) (i : Fin n)
    (w : Option (E.S i)) : (k : Fin n) → Option (E.S k) :=
  Function.update (fun k => some (v k)) i w

end Supplement

end DSICCompComp



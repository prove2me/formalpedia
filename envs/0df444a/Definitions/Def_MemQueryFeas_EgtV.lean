-- Prove2me | Definitions.Def_MemQueryFeas_EgtV
-- name    : MemQueryFeas_EgtV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:13.848696+00:00
-- url     : https://prove2.me/theorems/accaa9fd-bd28-4e2b-82ee-9ca5e8c3ef76
-- title:
--   Deeper base subspaces $E_{>p}$
-- statement:
--   $E_{>p}=(E_{p+1},\dots,E_P)$, the base subspaces of the layers deeper than $p$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Theorem 2 and Definition 4, pp.10–11

import Mathlib
import Definitions.Def_MemQueryFeas_Op

namespace MemQueryFeas

/-- **The deeper base subspaces `E_{>p}`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Theorem 2 and Definition 4, pp.10–11: the context
variable `E_{>p} = (E_{p+1}, …, E_P)`.

`EgtV Eb P p q = Eb q` for `p < q ≤ P` and `0` otherwise. -/
def EgtV {d : ℕ} (Eb : ℕ → Op d) (P p : ℕ) : ℕ → Op d :=
  fun q => if p < q ∧ q ≤ P then Eb q else 0

end MemQueryFeas



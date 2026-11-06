-- Prove2me | Definitions.Def_MemQueryFeas_dt
-- name    : MemQueryFeas_dt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:45.424195+00:00
-- url     : https://prove2.me/theorems/0536153b-dfb1-47ce-abe7-fd3276e61572
-- title:
--   The subspace dimension $\tilde d$
-- statement:
--   $\tilde d=\lfloor d/(36P)\rfloor$, the dimension of the hidden subspaces $E_1,\dots,E_P$ of a depth-$P$ construction.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), §3.1, p.7 (PDF p.8)

import Mathlib

namespace MemQueryFeas

/-- **The subspace dimension `d̃`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), §3.1, p.7 (PDF p.8): "`E_1, …, E_P` iid
`∼ Unif(Gr(d̃, d))`, where `d̃ := ⌊d/(36P)⌋`."

**Formalization Note.** Natural-number division is the floor. -/
def dt (d P : ℕ) : ℕ := d / (36 * P)

end MemQueryFeas



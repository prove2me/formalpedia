-- Prove2me | Definitions.Def_MemQueryFeas_truncSeq
-- name    : MemQueryFeas_truncSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:17.23224+00:00
-- url     : https://prove2.me/theorems/0d9a8c30-caa3-4435-a83c-c4e65f229cc8
-- title:
--   Truncated sequence $u^{(<n)}$
-- statement:
--   For a sequence $u^{(0)},u^{(1)},\dots$ of subspaces, $u^{(<n)}$ keeps the entries with index $j<n$ (the others are replaced by $0$). Thus $E^{(\le i)}=E^{(<i+1)}$ and $E^{(<i)}$ are the versions with index at most $i$, respectively less than $i$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Notations, p.7 (PDF p.8); Game 1, p.12

import Mathlib
import Definitions.Def_MemQueryFeas_Op

namespace MemQueryFeas

/-- **Truncated sequence `u^(<n)`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Notations, p.7 (PDF p.8): "the shorthand `u^(≤N)` to refer
to a given sequence `(u^(1), …, u^(N))`"; also `E^(<i)` and `E^(≤i)` in Game 1 (p.12).

`truncSeq n s` keeps the entries `s j` with `j < n` and replaces the others by `0`, so it carries
exactly the information of `(s 0, …, s (n − 1))`. `E^(≤i)` is `truncSeq (i+1)` and `E^(<i)` is
`truncSeq i`.

**Formalization Note.** Sequences of subspaces are indexed from `0` (NoiseAddition outputs
`F^(0), …, F^(N)`). -/
def truncSeq {d : ℕ} (n : ℕ) (s : ℕ → Op d) : ℕ → Op d :=
  fun j => if j < n then s j else 0

end MemQueryFeas



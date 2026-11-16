-- Prove2me | Definitions.Def_CompDesign_Supplement_blockCount
-- name    : CompDesign_Supplement_blockCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:51:06.066107+00:00
-- url     : https://prove2.me/theorems/3b723141-a418-4a76-aa01-993bc3cb3ff4
-- title:
--   Number of blocks $q=\lceil m/\min\{m,\lfloor1/\lambda\rfloor\}\rceil$
-- statement:
--   For $m$ actions and a large-market parameter $\lambda\in(0,1]$, set $k=\min\{m,\lfloor1/\lambda\rfloor\}$ and
--   $$q=\Big\lceil\frac mk\Big\rceil.$$
--   This is the quantity of Theorem 7.3 and of (54).
--
--   **Formalization Note** For $m\ge1$ and $0<\lambda\le1$, $k\ge1$; at $m=0$ the value is $0$, where every statement using it is trivial.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), §7.1.2, p.55 (PDF 58); (54), p.60 (PDF 63)

import Mathlib

namespace CompDesign.Supplement

/-- The number of blocks `q = ⌈m/k⌉` with `k = min{m, ⌊1/λ⌋}` of §7.1.2, p.55 (PDF 58), and (54),
p.60 (PDF 63), of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…).

**Formalization Note.** `λ` is written `l`. For `m ≥ 1` and `0 < l ≤ 1` we have `k ≥ 1`, so the
division is genuine; at `m = 0` the value is `0`, where every statement using it is trivial. -/
noncomputable def blockCount (m : ℕ) (l : ℝ) : ℕ :=
  ⌈(m : ℝ) / ((min m ⌊1 / l⌋₊ : ℕ) : ℝ)⌉₊

end CompDesign.Supplement



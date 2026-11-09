-- Prove2me | Definitions.Def_IntADSat_tP
-- name    : IntADSat_tP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:32.545552+00:00
-- url     : https://prove2.me/theorems/9ed9f83e-c617-4058-93da-bdf20ed55943
-- title:
--   Threshold $t=\lfloor (n-1)/2-\sqrt{0.245\,n\log n}\rfloor$ of (B.1)
-- statement:
--   The degree threshold of display (B.1): for $n\in\mathbb N$,
--
--   $$
--   t=\Big\lfloor \frac{n-1}{2}-\sqrt{0.245\,n\log n}\Big\rfloor ,
--   $$
--
--   with the natural logarithm. Vertices of degree at most $t$ are the "low-degree" vertices of the second round of the construction.
--
--   **Formalization Note** `Int.floor` (the value is negative for small $n$).
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), display (B.1), p.16 (PDF 17)

import Mathlib

set_option autoImplicit false

namespace IntADSat

/-- The threshold `t = ⌊(n − 1)/2 − √(0.245 n log n)⌋` of display (B.1)
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.16 (PDF 17)).

**Formalization Note** `Int.floor` (the value is negative for small `n`); `log` is the natural
logarithm ("All logarithms below, unless a base is indicated, are natural", p.15). -/
noncomputable def tP (n : ℕ) : ℤ :=
  ⌊((n : ℝ) - 1) / 2 - Real.sqrt (0.245 * n * Real.log n)⌋

end IntADSat



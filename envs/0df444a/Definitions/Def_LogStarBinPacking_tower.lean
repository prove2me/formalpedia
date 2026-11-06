-- Prove2me | Definitions.Def_LogStarBinPacking_tower
-- name    : LogStarBinPacking_tower
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:11.712815+00:00
-- url     : https://prove2.me/theorems/e1a5ebe6-6e8f-4d55-a3d9-35130041836a
-- title:
--   The tower sequence $T_0=2$, $T_{j+1}=2^{T_j}$
-- statement:
--   The **tower sequence** is defined by
--   $$
--   T_0=2,\qquad T_{j+1}=2^{T_j}\quad(j\ge0).
--   $$
--   So $T_1=4$, $T_2=16$, $T_3=65536$.
--
--   It measures the size of the competing trees of the [OAI26] construction (Lemma 3.2: $S_d\le T_{4d+2}$) and is inverse to the iterated logarithm: $T_{h-2}<n\le T_{h-1}$ exactly when $\log^* n=h$.
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), (3.2), p.13

import Mathlib

namespace LogStarBinPacking

/-- **The tower sequence (3.2).** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three
Items per Bin*, manuscript (sha256 1d88425d…), (3.2), p.13: `T₀ = 2` and `T_{j+1} = 2^{T_j}` for
`j ≥ 0`.

**Formalization Note** The sequence is indexed by `ℕ`, with values in `ℕ`. -/
def tower : ℕ → ℕ
  | 0 => 2
  | j + 1 => 2 ^ tower j

end LogStarBinPacking



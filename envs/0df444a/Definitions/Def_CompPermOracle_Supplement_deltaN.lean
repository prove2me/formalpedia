-- Prove2me | Definitions.Def_CompPermOracle_Supplement_deltaN
-- name    : CompPermOracle_Supplement_deltaN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:47:13.242728+00:00
-- url     : https://prove2.me/theorems/0546929d-571b-43a0-bd47-ae09126ae122
-- title:
--   The error terms $\delta_N(T)$, $a_N(T)$ and $e_N(T)$
-- statement:
--   For natural numbers $N$ and $T$ with $3T-1\le N$, the state-distance error of the soundness theorem is
--   $$
--   \delta_N(T)=\frac{60T}{\sqrt{N-T+1}}+\frac{T(T+1)}{2(N-2T+1)},
--   $$
--   half the right-hand side of the distinguishing bound (13). For the applications one also writes
--   $$
--   a_N(T)=\sqrt{\frac{N}{N-T}},\qquad e_N(T)=T\sqrt{\frac{2}{N-T}}+\delta_N(T).
--   $$
--   By (31), the final compressed state of a $T$-query computation is within Euclidean distance $\delta_N(T)$ of the image of the purified state; this is the error added to the square root of a success probability in the search bounds of Section 5.
--
--   **Formalization Note** $N$ and $T$ are natural numbers cast to the reals, so no difference such as $N-T$ is truncated. The source uses these quantities only when $3T-1\le N$, where all denominators are positive, and every theorem using them carries that hypothesis.
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), eq. (80), p.27; eq. (87), p.30

import Mathlib

namespace CompPermOracle.Supplement

/-- The state-distance error `δ_N(T) = 60T/√(N − T + 1) + T(T + 1)/(2(N − 2T + 1))` (Carolan,
Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256
52ebc507…), §5, eq. (80), p.27). It is half the right side of display (13).

**Formalization Note.** `N` and `T` are natural numbers cast to `ℝ`, and all arithmetic is real, so
`N − T + 1` and `N − 2T + 1` are never truncated. The source uses `δ_N(T)` only when
`3T − 1 ≤ N`, where both denominators are positive; every statement of this mission carries that
hypothesis. -/
noncomputable def deltaN (N T : ℕ) : ℝ :=
  60 * (T : ℝ) / Real.sqrt ((N : ℝ) - T + 1) + (T : ℝ) * ((T : ℝ) + 1) / (2 * ((N : ℝ) - 2 * T + 1))

/-- `a_N(T) = √(N/(N − T))` (arXiv:2609.28469, eq. (87), p.30). Real arithmetic. -/
noncomputable def aN (N T : ℕ) : ℝ :=
  Real.sqrt ((N : ℝ) / ((N : ℝ) - T))

/-- `e_N(T) = T√(2/(N − T)) + δ_N(T)` (arXiv:2609.28469, eq. (87), p.30). Real arithmetic. -/
noncomputable def eN (N T : ℕ) : ℝ :=
  (T : ℝ) * Real.sqrt (2 / ((N : ℝ) - T)) + deltaN N T

end CompPermOracle.Supplement



-- Prove2me | Definitions.Def_AvgPHETH_Supplement_JPar
-- name    : AvgPHETH_Supplement_JPar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:34:52.629802+00:00
-- url     : https://prove2.me/theorems/c6e28fae-de1c-447f-a722-4cf9324cc08c
-- title:
--   The completion deadline $J_k(n)=\lceil\log a_k(n)/4\rceil+4$
-- statement:
--   For $k,n\in\mathbb N$,
--
--   $$J_k(n)=\Big\lceil\frac{\log a_k(n)}4\Big\rceil+4 .$$
--
--   It is the stage by which the variables of a reserved group $(k,n)$, which determine the answers of $V_k$ on inputs of length $n$, are completely assigned.
--
--   **Formalization Note** $\log$ is $\log_2$. For an active pair, $a_k(n)\ge\lfloor\sqrt n\rfloor\ge4$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Parameters", p.39 (PDF 41), item 4

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_aPar

namespace AvgPHETH.Supplement

/-- The completion deadline `J_k(n) = ⌈(log a_k(n))/4⌉ + 4`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Parameters", item 4, p.39 (PDF 41)). `log` is `log₂`.

**Formalization Note** For active `(k, n)`, `a_k(n) ≥ ⌊√n⌋ ≥ 4`, so the logarithm is of a number `≥ 4`. -/
noncomputable def JPar (ε : ℕ → ℝ) (k n : ℕ) : ℕ := ⌈Real.logb 2 (aPar ε k n) / 4⌉₊ + 4

end AvgPHETH.Supplement



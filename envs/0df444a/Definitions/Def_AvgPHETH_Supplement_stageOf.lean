-- Prove2me | Definitions.Def_AvgPHETH_Supplement_stageOf
-- name    : AvgPHETH_Supplement_stageOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:35:12.958142+00:00
-- url     : https://prove2.me/theorems/4c8e4189-d63d-4d90-8666-f5f9a18ea84f
-- title:
--   The stage $i(T)=\max\{1,\lfloor\log\log T/4\rfloor\}$ of an $A$-query
-- statement:
--   For a time parameter $T$,
--
--   $$i(T)=\max\Big\{1,\Big\lfloor\frac{\log\log T}4\Big\rfloor\Big\}.$$
--
--   All queries to the help oracle $A$ with time parameter $T$ are assigned in stage $i(T)$ of the construction.
--
--   **Formalization Note** $\log$ is $\log_2$. Valid queries have $T\ge2$, where $\log\log T\ge0$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "The construction", p.40 (PDF 42)

import Mathlib

namespace AvgPHETH.Supplement

/-- The stage `i(T) = max{1, ⌊(log log T)/4⌋}` in which the `A`-queries with time parameter `T` are
assigned (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "The construction", p.40 (PDF 42)). `log` is `log₂`.

**Formalization Note** Valid `A`-queries have `T ≥ 2`, where `log log T ≥ 0`. -/
noncomputable def stageOf (T : ℕ) : ℕ := max 1 ⌊Real.logb 2 (Real.logb 2 T) / 4⌋₊

end AvgPHETH.Supplement



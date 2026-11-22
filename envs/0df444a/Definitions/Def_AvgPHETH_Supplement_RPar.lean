-- Prove2me | Definitions.Def_AvgPHETH_Supplement_RPar
-- name    : AvgPHETH_Supplement_RPar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:32:34.276845+00:00
-- url     : https://prove2.me/theorems/f0774202-0abe-4c8e-a5cf-c588d169a990
-- title:
--   The parameter $R(n)=g(n)\log n$
-- statement:
--   For $\varepsilon:\mathbb N\to\mathbb R$ and $n\in\mathbb N$,
--
--   $$R(n)=g(n)\,\log n,$$
--
--   where $g(n)=\max\{16,\lceil\log(1/\varepsilon(n))\rceil\}$. Each level of a selector tree shortens the index length by the factor $R(n)$.
--
--   **Formalization Note** $\log$ is $\log_2$, and $R(n)$ is a real number.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Parameters", p.39 (PDF 41)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_gPar

namespace AvgPHETH.Supplement

/-- The parameter `R(n) = g(n) · log n` of the oracle construction
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Parameters", p.39 (PDF 41)). `log` is `log₂`. -/
noncomputable def RPar (ε : ℕ → ℝ) (n : ℕ) : ℝ := (gPar ε n : ℝ) * Real.logb 2 n

end AvgPHETH.Supplement



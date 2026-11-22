-- Prove2me | Definitions.Def_AvgPHETH_Supplement_gPar
-- name    : AvgPHETH_Supplement_gPar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:32:06.145842+00:00
-- url     : https://prove2.me/theorems/420d29f2-4287-4af2-8d16-428b1b497284
-- title:
--   The parameter $g(n)=\max\{16,\lceil\log(1/\varepsilon(n))\rceil\}$
-- statement:
--   For a function $\varepsilon:\mathbb N\to\mathbb R$ with positive values, the oracle construction of Section 8 uses the integer parameter
--
--   $$g(n)=\max\Big\{16,\Big\lceil\log\frac1{\varepsilon(n)}\Big\rceil\Big\}.$$
--
--   It measures how slowly $\varepsilon(n)$ tends to $0$; all other parameters of the construction are defined from it.
--
--   **Formalization Note** $\log$ is $\log_2$. The natural-number ceiling is $0$ on negative reals, which the maximum with $16$ absorbs.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Parameters", p.39 (PDF 41)

import Mathlib

namespace AvgPHETH.Supplement

/-- The parameter `g(n) = max{16, ⌈log(1/ε(n))⌉}` of the oracle construction
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Parameters", p.39 (PDF 41)).

**Formalization Note** `log` is `log₂`. The natural-number ceiling `⌈·⌉₊` is `0` on negative reals,
which the maximum with `16` absorbs. `ε(n) > 0` is a hypothesis wherever `g` is used. -/
noncomputable def gPar (ε : ℕ → ℝ) (n : ℕ) : ℕ := max 16 ⌈Real.logb 2 (1 / ε n)⌉₊

end AvgPHETH.Supplement



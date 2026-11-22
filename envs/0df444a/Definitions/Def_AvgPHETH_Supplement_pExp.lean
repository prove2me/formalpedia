-- Prove2me | Definitions.Def_AvgPHETH_Supplement_pExp
-- name    : AvgPHETH_Supplement_pExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:34:08.347015+00:00
-- url     : https://prove2.me/theorems/439f04d3-92ca-4fa5-87dd-8a6ea5807d5d
-- title:
--   The exponent of the restriction probability $p_j(n)=2^{-\lceil a_{j+1}(n)g(n)^{1/2}\rceil}$
-- statement:
--   For $0\le j<k$ the random restrictions of the oracle construction use the probability
--
--   $$p_j(n)=2^{-\lceil a_{j+1}(n)\,g(n)^{1/2}\rceil}.$$
--
--   This definition is its exponent $\lceil a_{j+1}(n)\sqrt{g(n)}\rceil$.
--
--   **Formalization Note** Only the exponent $b$ is stored: a $p_j$-random restriction of $N$ variables leaves $\lfloor p_jN\rfloor=\lfloor N/2^{b}\rfloor$ of them unset.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Parameters", p.39 (PDF 41), item 3

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_aPar
import Definitions.Def_AvgPHETH_Supplement_gPar

namespace AvgPHETH.Supplement

/-- The exponent `⌈a_{j+1}(n) · g(n)^{1/2}⌉` of the restriction probability
`p_j(n) = 2^{−⌈a_{j+1}(n) g(n)^{1/2}⌉}`, for `0 ≤ j < k`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Parameters", item 3, p.39 (PDF 41)).

**Formalization Note** Only the exponent is stored: a `p_j`-random restriction of `N` variables leaves
`⌊p_j N⌋ = N / 2^{pExp}` (natural-number division) of them unset. -/
noncomputable def pExp (ε : ℕ → ℝ) (j n : ℕ) : ℕ :=
  ⌈(aPar ε (j + 1) n : ℝ) * Real.sqrt (gPar ε n)⌉₊

end AvgPHETH.Supplement



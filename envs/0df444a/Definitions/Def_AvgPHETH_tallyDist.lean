-- Prove2me | Definitions.Def_AvgPHETH_tallyDist
-- name    : AvgPHETH_tallyDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:26:13.319736+00:00
-- url     : https://prove2.me/theorems/c1929303-14c6-4f41-b71f-28b919d78bb1
-- title:
--   The tally family $\mathcal T=\{\mathcal T_n\}$
-- statement:
--   $\mathcal T_n$ is the distribution supported on the single string $1^n$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.5, p.18 (PDF 20)

import Mathlib
import Definitions.Def_AvgPHETH_unary

namespace AvgPHETH

/-- The tally family `T = {T_n}`: `T_n` is supported on `{1^n}` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.5, p.18 (PDF 20)). -/
noncomputable def tallyDist (n : ℕ) : PMF (List Bool) := PMF.pure (unary n)

end AvgPHETH



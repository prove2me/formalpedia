-- Prove2me | Definitions.Def_AvgPHETH_uniformDist
-- name    : AvgPHETH_uniformDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:24:59.188716+00:00
-- url     : https://prove2.me/theorems/8f96b7b2-a032-4d8f-a721-d9a565346ee2
-- title:
--   The uniform family $\mathcal U=\{\mathcal U_n\}$
-- statement:
--   $\mathcal U_n$ is the uniform distribution on $\{0,1\}^n$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.5, p.18 (PDF 20)

import Mathlib

namespace AvgPHETH

/-- The uniform family `U = {U_n}`: `U_n` is uniform on `{0,1}^n` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.5, p.18 (PDF 20)). -/
noncomputable def uniformDist (n : ℕ) : PMF (List Bool) :=
  (PMF.uniformOfFintype (Fin n → Bool)).map List.ofFn

end AvgPHETH



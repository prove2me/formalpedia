-- Prove2me | Definitions.Def_AvgPHETH_AvgPDist
-- name    : AvgPHETH_AvgPDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:29:45.806553+00:00
-- url     : https://prove2.me/theorems/ff1d3d9e-f68d-4917-b4f3-51b9e5d8e1fa
-- title:
--   The class $\mathrm{AvgP}^O$
-- statement:
--   A distributional problem $(L,D)$ is in $\mathrm{AvgP}^O$ if it has an errorless heuristic scheme with oracle $O$. For $O=\emptyset$ this is $\mathrm{AvgP}$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Definition 4.1, p.14 (PDF 16), and p.15 (PDF 17)

import Mathlib
import Definitions.Def_AvgPHETH_IsHeuristicScheme
open KarpLiptonOM

namespace AvgPHETH

/-- `(L, D) ∈ AvgP^O`: the distributional problem has an errorless heuristic scheme with oracle `O`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Definition 4.1, p.14 (PDF 16), and p.15 (PDF 17): "For an oracle `O`, `AvgP^O` is defined in
the same way, where `A` may query `O`"). -/
def AvgPDist (O L : Set (List Bool)) (D : ℕ → PMF (List Bool)) : Prop :=
  ∃ (M : OracleTM) (e : ℕ), IsHeuristicScheme O L D M e

end AvgPHETH



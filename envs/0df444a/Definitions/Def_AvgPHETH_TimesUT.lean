-- Prove2me | Definitions.Def_AvgPHETH_TimesUT
-- name    : AvgPHETH_TimesUT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:31:43.175417+00:00
-- url     : https://prove2.me/theorems/5b5a8155-1f51-480a-a752-0b22f18fe4b1
-- title:
--   $\mathcal C\times\{\mathcal U,\mathcal T\}\subseteq\mathrm{AvgP}^O$
-- statement:
--   The statement that for every language $L$ in the class $\mathcal C$, both $(L,\mathcal U)$ and $(L,\mathcal T)$ are in $\mathrm{AvgP}^O$. This assumption involves no distribution whose sampler queries $O$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 4.7, p.18 (PDF 20); p.30 (PDF 32)

import Mathlib
import Definitions.Def_AvgPHETH_AvgPDist
import Definitions.Def_AvgPHETH_uniformDist
import Definitions.Def_AvgPHETH_tallyDist

namespace AvgPHETH

/-- `C × {U, T} ⊆ AvgP^O`: for every `L ∈ C`, both `(L, U)` and `(L, T)` are in `AvgP^O`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 4.7, p.18 (PDF 20); p.30 (PDF 32)). -/
def TimesUT (O : Set (List Bool)) (C : Set (Set (List Bool))) : Prop :=
  ∀ L ∈ C, AvgPDist O L uniformDist ∧ AvgPDist O L tallyDist

end AvgPHETH



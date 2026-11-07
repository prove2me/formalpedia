-- Prove2me | Definitions.Def_AvgPHETH_Delta2PO
-- name    : AvgPHETH_Delta2PO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:47.3002+00:00
-- url     : https://prove2.me/theorems/110c3749-269c-4926-a242-3c028e739d6b
-- title:
--   The class $\Delta_2^{p,O}=\mathrm{P}^{\mathrm{NP}^O}$
-- statement:
--   The class of languages decidable in polynomial time with an oracle in $\mathrm{NP}^O=\Sigma_1^{p,O}$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 4.8, p.18 (PDF 20)

import Mathlib
import Definitions.Def_AvgPHETH_SigmaPO
import Definitions.Def_AvgPHETH_PO

namespace AvgPHETH

/-- The class `Δ₂^{p,O} = P^{NP^O}`: languages decidable in polynomial time with an oracle `B` in
`NP^O` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 4.8, p.18 (PDF 20)).

**Formalization Note** The machine has one oracle `B ∈ NP^O`; a query to `O` itself is covered, since
`O` and a language in `NP^O` join to one language in `NP^O`. -/
def Delta2PO (O : Set (List Bool)) : Set (Set (List Bool)) :=
  {L | ∃ B ∈ SigmaPO O 1, PO B L}

end AvgPHETH



-- Prove2me | Definitions.Def_AvgPHETH_Supplement_oracleOf
-- name    : AvgPHETH_Supplement_oracleOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:41:47.196515+00:00
-- url     : https://prove2.me/theorems/93930be1-7d46-4494-a5b0-bcdfe1ce5d38
-- title:
--   The oracle $O=A+V$
-- statement:
--   The oracle of Section 8 has two components: $V$, which facilitates diagonalization, and $A$, an average-case help oracle. This definition is the oracle $O=A+V$ with the $A$-answers of a given table and the $V$-answers determined by a given assignment to the construction variables.
--
--   **Formalization Note** $A+V$ is the published two-component join of the two languages.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, p.38 (PDF 40)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_ASet
import Definitions.Def_AvgPHETH_Supplement_VSet
import Definitions.Def_AvgPHETH_oJoin

namespace AvgPHETH.Supplement

open AvgPHETH

/-- The oracle `O = A + V` with the `A`-answers of the table `tab` and the `V`-answers given by the
assignment `β` to the construction variables
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, p.38 (PDF 40): "our oracle has two components: `V`, which facilitates
diagonalization, and `A`, an average-case 'help' oracle").

**Formalization Note** `A + V` is the published two-component join `AvgPHETH.oJoin` of the languages
`ASet tab` and `VSet ε β`. -/
def oracleOf (ε : ℕ → ℝ) (tab : ℕ → ℕ → List Bool → ℕ → Option Bool) (β : CVar → List Bool) :
    Set (List Bool) :=
  oJoin (ASet tab) (VSet ε β)

end AvgPHETH.Supplement



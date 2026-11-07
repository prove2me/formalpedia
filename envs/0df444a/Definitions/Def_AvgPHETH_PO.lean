-- Prove2me | Definitions.Def_AvgPHETH_PO
-- name    : AvgPHETH_PO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:28:53.470028+00:00
-- url     : https://prove2.me/theorems/214b6568-caa9-42ae-813c-6e2c7c051cc8
-- title:
--   The class $\mathrm{P}^O$
-- statement:
--   A language $L$ is in $\mathrm{P}^O$ if a single deterministic machine with oracle $O$ decides it, halting on every input $x$ within $|x|^e+e$ steps for a constant $e$.
--
--   **Formalization Note** The time bound is required for the oracle $O$ only, not for every oracle.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), used throughout; §4.2, p.15 (PDF 17)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_AvgPHETH_acceptsAt
open KarpLiptonOM

namespace AvgPHETH

/-- `L ∈ P^O`: one deterministic machine with oracle `O` decides `L` in time polynomial in `|x|`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), used throughout; §4.2, p.15 (PDF 17)).

**Formalization Note** The time bound is required for this oracle `O` only. The published
`KarpLiptonOM.OracleTM.IsPolyTime` demands it for every oracle, which is not what is needed here:
a machine of an errorless scheme or a solver is fast for its own oracle. -/
def PO (O L : Set (List Bool)) : Prop :=
  ∃ (M : OracleTM) (e : ℕ), ∀ x : List Bool,
    M.HaltsWithin O (x.length ^ e + e) (tupleEnc [x]) ∧
      (x ∈ L ↔ acceptsAt M O (x.length ^ e + e) (tupleEnc [x]))

end AvgPHETH



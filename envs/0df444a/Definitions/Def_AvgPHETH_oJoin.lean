-- Prove2me | Definitions.Def_AvgPHETH_oJoin
-- name    : AvgPHETH_oJoin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:15.670235+00:00
-- url     : https://prove2.me/theorems/0d7b46be-b037-4df9-b584-a53e1e838a1c
-- title:
--   The join $O\oplus A$ of two oracles
-- statement:
--   For languages $O$ and $A$, the join $O\oplus A$ is the language of strings $\langle i,q\rangle$ with $q\in O$ for $i=1$ and $q\in A$ for $i=2$, where $i$ is written as a fixed-width tag. An oracle for $O\oplus A$ answers queries to either language.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 4.7, p.18 (PDF 20)

import Mathlib
import Definitions.Def_KarpLiptonOM_langJoin
open KarpLiptonOM

namespace AvgPHETH

/-- The join `O ⊕ A` of two oracle languages (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 4.7, p.18 (PDF 20)).

**Formalization Note** This is the published two-component join `KarpLiptonOM.langJoin`: a query
`⟨i, q⟩` starts with the one-hot tag of `i`. -/
def oJoin (O A : Set (List Bool)) : Set (List Bool) := langJoin ![O, A]

end AvgPHETH



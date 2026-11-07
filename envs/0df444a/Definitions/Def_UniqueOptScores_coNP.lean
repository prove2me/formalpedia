-- Prove2me | Definitions.Def_UniqueOptScores_coNP
-- name    : UniqueOptScores_coNP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:28:12.961409+00:00
-- url     : https://prove2.me/theorems/816793eb-ab6f-4c06-aa4e-87f80713768d
-- title:
--   The class $\mathrm{coNP}^A$
-- statement:
--   $\mathrm{coNP}^A$ consists of the complements $\{0,1\}^* \setminus L$ of the languages $L \in \mathrm{NP}^A$.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 3.2, p.13 and p.15 (Proposition 3.2)

import Mathlib
import Definitions.Def_UniqueOptScores_NP

namespace UniqueOptScores

/-- **The class coNP^A**: complements of languages of NP^A.
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §3.2, p.13 and p.15 (Proposition 3.2). -/
def coNP (A : Set (List Bool)) : Set (Set (List Bool)) :=
  {L | Lᶜ ∈ NP A}

end UniqueOptScores



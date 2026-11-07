-- Prove2me | Definitions.Def_UniqueOptScores_DP
-- name    : UniqueOptScores_DP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:29:08.937214+00:00
-- url     : https://prove2.me/theorems/5e930abf-8fc7-4f66-8d70-a3cec9fb03a9
-- title:
--   The class $\mathrm{DP}^A$
-- statement:
--   The class $\mathrm{DP}^A$ consists of the languages expressible as the intersection of an $\mathrm{NP}^A$ language and a $\mathrm{coNP}^A$ language:
--   $$
--   \mathrm{DP}^A = \{L_1 \cap L_2 : L_1 \in \mathrm{NP}^A,\ L_2 \in \mathrm{coNP}^A\}.
--   $$
--   Classes defined by Boolean combinations are relativized by relativizing their constituents (p.15).
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 3.2, p.13 ("DP := {L1 ∩ L2 : L1 ∈ NP, L2 ∈ coNP}") and p.15

import Mathlib
import Definitions.Def_UniqueOptScores_NP
import Definitions.Def_UniqueOptScores_coNP

namespace UniqueOptScores

/-- **The class DP^A.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §3.2, p.13: "DP := {L1 ∩ L2 : L1 ∈ NP, L2 ∈ coNP}", relativized by relativizing the
constituent classes (p.15). -/
def DP (A : Set (List Bool)) : Set (Set (List Bool)) :=
  {L | ∃ L₁ ∈ NP A, ∃ L₂ ∈ coNP A, L = L₁ ∩ L₂}

end UniqueOptScores



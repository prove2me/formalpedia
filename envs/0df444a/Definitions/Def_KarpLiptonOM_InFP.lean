-- Prove2me | Definitions.Def_KarpLiptonOM_InFP
-- name    : KarpLiptonOM_InFP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:42.05663+00:00
-- url     : https://prove2.me/theorems/26bf94d5-a9e0-4f9f-801d-da01b23d9c29
-- title:
--   Search problem $R \in \mathrm{FP}^\Pi$ (Definition A.2.1)
-- statement:
--   A search problem, i.e. a relation $R(x, y)$ between inputs and solutions, is in $\mathrm{FP}^\Pi$ if there is a deterministic polynomial-time oracle transducer $M$ such that for every language $O$ consistent with $\Pi$ and every input $x$,
--   $$
--   R\bigl(x, M^O(x)\bigr).
--   $$
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Definition A.2.1, p.21

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_IsPolyTime
import Definitions.Def_KarpLiptonOM_OracleTM_out
import Definitions.Def_KarpLiptonOM_Consistent
import Definitions.Def_KarpLiptonOM_tupleEnc

namespace KarpLiptonOM

/-- A search problem (relation) `R` is in `FP^Π` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), Definition A.2.1, p.21): a deterministic
polynomial-time oracle machine `M` such that, for every `O` consistent with `Π` and every input `x`,
`M^O(x)` is a solution for `x`. -/
def InFP (PP : PromiseProblem) (R : List Bool → List Bool → Prop) : Prop :=
  ∃ (M : OracleTM) (k : ℕ), M.IsPolyTime k ∧
    ∀ O, Consistent O PP → ∀ x : List Bool, R x (M.out O k (tupleEnc [x]))

end KarpLiptonOM



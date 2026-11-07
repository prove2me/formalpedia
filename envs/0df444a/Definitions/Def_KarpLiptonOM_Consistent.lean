-- Prove2me | Definitions.Def_KarpLiptonOM_Consistent
-- name    : KarpLiptonOM_Consistent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:59.770999+00:00
-- url     : https://prove2.me/theorems/2acbd573-1082-4f7d-8b86-01f0dbd64d31
-- title:
--   Language consistent with a promise problem
-- statement:
--   A language $O$ is **consistent** with a promise problem $\Pi$ if
--   $$
--   \Pi_{\mathrm{YES}} \subseteq O \quad\text{and}\quad \Pi_{\mathrm{NO}} \cap O = \emptyset .
--   $$
--   Oracle access to a promise problem is through consistent languages: a computation with oracle $\Pi$ must be correct for every consistent $O$ (loose access, in the form the paper fixes for deterministic machines).
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.2, p.21

import Mathlib
import Definitions.Def_KarpLiptonOM_PromiseProblem

namespace KarpLiptonOM

/-- A language `O` is **consistent** with a promise problem `Π` if `Π_YES ⊆ O` and `Π_NO ∩ O = ∅`
(Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.2, p.21). -/
def Consistent (O : Set (List Bool)) (PP : PromiseProblem) : Prop :=
  PP.yes ⊆ O ∧ Disjoint O PP.no

end KarpLiptonOM



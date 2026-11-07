-- Prove2me | Definitions.Def_KarpLiptonOM_IsTally
-- name    : KarpLiptonOM_IsTally
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:23.556169+00:00
-- url     : https://prove2.me/theorems/cb6d6808-1bdd-4bc4-8ea3-e6c5892fbd3b
-- title:
--   Tally language $T \subseteq \{1\}^*$
-- statement:
--   A language $T$ is **tally** if every string in it consists of ones only, $T \subseteq \{1\}^*$. TALLY denotes the class of tally languages.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20

import Mathlib

namespace KarpLiptonOM

/-- A language `T` is **tally** if `T ⊆ {1}*` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20). -/
def IsTally (T : Set (List Bool)) : Prop := ∀ w ∈ T, ∀ b ∈ w, b = true

end KarpLiptonOM



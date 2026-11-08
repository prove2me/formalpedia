-- Prove2me | Definitions.Def_QWildMatch_SearchCorrect
-- name    : QWildMatch_SearchCorrect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:15:21.090484+00:00
-- url     : https://prove2.me/theorems/09b03f71-ff01-4ee6-8d53-1bb3aa0b86aa
-- title:
--   Correctness of a search output over $N$ indices
-- statement:
--   For a Boolean function $g$ on $N$ indices, an output $i$ is correct when $g(i)=1$, and the output "none" is correct when $g$ vanishes everywhere. This is the output semantics of a bounded-error search in the find form: either a marked index, or the claim that there is none.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), Lemma 3.3, p.4

import Mathlib

namespace QWildMatch

/-- Correctness of a search output over `N` indices (Zhao et al., STOC 2027 submission, Lemma 3.3,
p.4): `none` claims no index is marked, and `some i` must be a marked index. -/
def SearchCorrect {N : ℕ} (g : Fin N → ZMod 2) : Option (Fin N) → Prop
  | none => ∀ i, g i = 0
  | some i => g i = 1

open Classical in
noncomputable instance {N : ℕ} (g : Fin N → ZMod 2) (o : Option (Fin N)) :
    Decidable (SearchCorrect g o) :=
  Classical.propDecidable _

end QWildMatch



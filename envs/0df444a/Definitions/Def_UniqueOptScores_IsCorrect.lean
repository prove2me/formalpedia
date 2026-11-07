-- Prove2me | Definitions.Def_UniqueOptScores_IsCorrect
-- name    : UniqueOptScores_IsCorrect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:28:27.886537+00:00
-- url     : https://prove2.me/theorems/c2a2a1ee-f263-4dc9-b199-9aecd082c459
-- title:
--   Correctness on $P_r$
-- statement:
--   A score system is **correct on $P_r$** if $U(S) = F(S)$ for every support $S \subseteq X \cup Y$ in $P_r$: on promised supports, a unique maximizing candidate exists exactly when one of the two regions contains exactly one present point.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 6, p.22 ("If U(S) = F(S) for every S ∈ P_r"; "assume correctness on P_r")

import Mathlib
import Definitions.Def_UniqueOptScores_QTree
import Definitions.Def_UniqueOptScores_supportOracle
import Definitions.Def_UniqueOptScores_HasUniqueMax
import Definitions.Def_UniqueOptScores_Fpred
import Definitions.Def_UniqueOptScores_InPr

namespace UniqueOptScores

/-- **Correctness on P_r.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §6, p.22: "If U(S) = F(S) for every S ∈ P_r"; "Throughout the proof assume correctness on
P_r."

`IsCorrect X Y e T r` holds when `U(S) ↔ F(S)` for every support `S ⊆ X ∪ Y` in `P_r`. -/
def IsCorrect {ι α : Type*} [DecidableEq α] [Fintype ι] (X Y : Finset α) (e : α → Bool)
    (T : ι → QTree α ℕ) (r : ℕ) : Prop :=
  ∀ S ⊆ X ∪ Y, InPr r X Y S → (HasUniqueMax T (supportOracle X Y e S) ↔ Fpred X Y S)

end UniqueOptScores



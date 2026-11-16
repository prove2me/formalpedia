-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_IsNormalised
-- name    : AgnosticTNS_Supplement_IsNormalised
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:26:28.43114+00:00
-- url     : https://prove2.me/theorems/0171aa61-ed09-496c-a093-0ee0063467f3
-- title:
--   Normalised learning sequence
-- statement:
--   A learning sequence $(S_i,I_i,F_i)_{i=1}^L$ is **normalised** if no step has $F_i=\emptyset$ and $|I_i|=1$. Such a step introduces no vertex and merely repeats its only child ($S_i=S_j$); normalisation removes these steps by identifying each with its child. A normalised sequence has length $L\le 2n-1$ (Remark 2.6).
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Remark 2.6, p.14

import Mathlib
import Definitions.Def_AgnosticTNS_LearningSequence

namespace AgnosticTNS.Supplement

/-- **A normalised learning sequence**, Remark 2.6, p.14 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
no step has `F_i = ∅` and `I_i = {j}` (such a step merely repeats its child and is removed). -/
def IsNormalised {n : ℕ} (Ls : LearningSequence n) : Prop :=
  ∀ i, ¬ (Ls.F i = ∅ ∧ (Ls.I i).card = 1)

end AgnosticTNS.Supplement



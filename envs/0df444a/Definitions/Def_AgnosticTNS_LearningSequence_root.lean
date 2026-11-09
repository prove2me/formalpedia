-- Prove2me | Definitions.Def_AgnosticTNS_LearningSequence_root
-- name    : AgnosticTNS_LearningSequence_root
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:10.03981+00:00
-- url     : https://prove2.me/theorems/3631866c-2285-4e1e-bf6b-20ddb10bcaa5
-- title:
--   Root of a learning sequence
-- statement:
--   The root of a learning sequence $(S_i,I_i,F_i)_{i=1}^L$ is its last step $L$ (in 0-based indexing, step $L-1$); $S_L=V$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definition 2.3, p.13

import Mathlib
import Definitions.Def_AgnosticTNS_LearningSequence

namespace AgnosticTNS

/-- **The root `L` of a learning sequence**, Definition 2.3 (4.), p.13 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): the last step,
`⟨L − 1, _⟩` in 0-based indexing. -/
def LearningSequence.root {n : ℕ} (Ls : LearningSequence n) : Fin Ls.L :=
  ⟨Ls.L - 1, by have := Ls.L_pos; omega⟩

end AgnosticTNS



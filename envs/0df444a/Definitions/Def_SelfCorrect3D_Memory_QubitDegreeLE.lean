-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_QubitDegreeLE
-- name    : SelfCorrect3D_Memory_QubitDegreeLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:13.917001+00:00
-- url     : https://prove2.me/theorems/1e1f1237-0a49-409c-adad-9e83f0240ceb
-- title:
--   Qubit degree at most $w$
-- statement:
--   A CSS code has **qubit degree at most $w$** if every qubit lies in the support of at most $w$ rows of $H_x$ and $H_z$ together, i.e. participates in at most $w$ checks (the LDPC condition of §2.1). For the paper's codes the maximum vertex degree is $z_v=7$.
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, §2.1, p. 10; p. 22

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_CSSCode

namespace SelfCorrect3D.Memory

/-- **Qubit degree at most `w`**: every qubit lies in the support of at most `w` rows of `H_x` and
`H_z` together. Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, §2.1, p. 10 ("each qubit participates in O(1)
checks", the LDPC condition); for the paper's codes `z_v = 7` (p. 22). -/
def QubitDegreeLE {n mX mZ : ℕ} (C : CSSCode n mX mZ) (w : ℕ) : Prop :=
  ∀ q, (Finset.univ.filter fun a => C.HX a q ≠ 0).card +
    (Finset.univ.filter fun b => C.HZ b q ≠ 0).card ≤ w

end SelfCorrect3D.Memory



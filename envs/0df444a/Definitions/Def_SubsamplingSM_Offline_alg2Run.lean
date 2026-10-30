-- Prove2me | Definitions.Def_SubsamplingSM_Offline_alg2Run
-- name    : SubsamplingSM_Offline_alg2Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:55:16.861978+00:00
-- url     : https://prove2.me/theorems/2bc09cbe-61bf-4706-89fa-51028d09a04b
-- title:
--   Final state of Algorithm 2 on given coins
-- statement:
--   For coins $b$ (with $b_u=1$ if and only if $u\in b$), the final state of Algorithm 2 is obtained by $n=|N|$ iterations from the initial state. Its fields are the final values of $S$, $O$, $O_u$ and $S_u$, to which every expression of the analysis refers ("every expression involving S or O is assumed to refer to the final values of these sets", p. 12).
--
--   **Formalization Note** Each effective iteration removes an element from $N'$, so the loop stops after at most $n$ iterations. For an element that is never considered, $S_u=O_u=\emptyset$.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Algorithm 2, p. 9, and p. 12

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_alg2Init
import Definitions.Def_SubsamplingSM_Offline_alg2Step

namespace SubsamplingSM.Offline

/-- **The final state of Algorithm 2 on given coins.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Algorithm 2, p. 9, and p. 12: "Throughout the remainder of this section, every expression
involving S or O is assumed to refer to the final values of these sets."

`alg2Run f I sel O₀ b` is the state after `n = |α|` iterations of `alg2Step` from
`alg2Init O₀`, with coins `b` (`b_u = 1` iff `u ∈ b`).

**Formalization Note.** Each effective iteration removes an element from `N′`, so the loop stops
after at most `n` iterations and later iterations change nothing; the fields of
`alg2Run f I sel O₀ b` are the final values of `S`, `O`, `O_u`, `S_u` (paper.md Reading 6).
For an element that is never considered, `S_u = O_u = ∅`. -/
noncomputable def alg2Run {α : Type*} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (sel : Finset α → Finset α → Finset α) (O₀ b : Finset α) :
    Alg2State α :=
  (alg2Step f I sel b)^[Fintype.card α] (alg2Init O₀)

end SubsamplingSM.Offline



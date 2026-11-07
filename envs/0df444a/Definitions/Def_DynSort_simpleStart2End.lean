-- Prove2me | Definitions.Def_DynSort_simpleStart2End
-- name    : DynSort_simpleStart2End
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:36:45.139635+00:00
-- url     : https://prove2.me/theorems/a0557ec7-f327-4fb8-9ce1-953168a20dfb
-- title:
--   The SimpleStart2End operation
-- statement:
--   **SimpleStart2End $(i)$** moves a hole from the first to the last cell of a level-$i$ section $S$:
--
--   1. If $i=1$, shift the elements of the sorted array to move the hole to its last position.
--   2. If $S$ is a single block with original section $O$, apply SimpleStart2End $(i-1)$ to $O$.
--   3. Otherwise, writing $S=O_1\mid T_2O_2\mid O_3$: apply SimpleStart2End $(i-1)$ to $O_1$; move $\min O_2$ into the hole in $O_1$ using InsertMax; apply SwapHole $(O_2,T_2)$, moving the hole to the end of $T_2$; and apply JumpDown $(i)$.
--
--   Each step is skipped once rebuilding has moved the hole to the end of $S$ or of an enclosing section. The operation applies only when $S$ is not the last original section of a three-block parent.
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), §4.5.1, p.17 (PDF p.19); p.13 (applicability)

import Mathlib
import Definitions.Def_DynSort_jumpDown

namespace DynSort

/-! # SimpleStart2End

Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.5.1, p.17 (PDF p.19).

Verbatim (p.17): "1. If i = 1, shift the elements of the sorted array to move the hole to its last
position. 2. If S contains a single block with original section O, invoke SimpleStart2End (i − 1)
on O. 3. Otherwise, write S = O1 | T2 | O2 | O3 and perform the following steps:
(a) Apply SimpleStart2End (i − 1) to O1, moving the hole to the end of O1.
(b) Move min O2 into the hole in O1 using InsertMax.
(c) Apply SwapHole (O2, T2) from right to left, moving the hole to the end of T2.
(d) Finally, apply JumpDown (i) to move the hole to the end of S."

**Formalization Note.** `simpleStart2End d i a st` acts on the level-`i` section at address `a`
of the level-`d` root; structural in `i`; truncated (`done`) after each sub-call, as in the Remark
of p.15. The operation "only applies when the DST is not the unique original section of a last
block" (p.13); the statements about it carry that hypothesis.
-/

variable {α : Type}

/-- **SimpleStart2End (i)** on the section at address `a` of a level-`d` root (p.17). -/
def simpleStart2End [LinearOrder α] (d : ℕ) : ℕ → List ℕ → St α → St α
  | 0, _, st => st
  | i + 1, a, st =>
    match st.root.get a with
    | some (.leaf _) => shiftToEnd a st
    | some (.single _) => simpleStart2End d i (a ++ [0]) st
    | some (.three ..) =>
      let st1 := simpleStart2End d i (a ++ [0]) st
      if done st1.root a then st1
      else
        let st2 := insertMax (a ++ [2]) (a ++ [0]) st1
        let st3 := swapHole d (a ++ [2]) (a ++ [1]) st2
        if done st3.root a then st3 else jumpDown d (i + 1) a st3
    | none => st

end DynSort



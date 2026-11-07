-- Prove2me | Definitions.Def_DynSort_jumpDown
-- name    : DynSort_jumpDown
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:35:46.43041+00:00
-- url     : https://prove2.me/theorems/56b09704-b256-4295-ad30-6f26e96e9880
-- title:
--   The JumpDown operation
-- statement:
--   **JumpDown $(i)$** acts on a three-block level-$i$ section $S=O_1\mid T_2O_2\mid O_3$ whose hole is the last cell of $T_2$, and moves the hole to the end of $S$:
--
--   1. If $O_3$ is a level-$1$ section, move $\min O_3$ into the hole in $T_2$ using InsertMax, and shift the elements of $O_3$ one position to the left to move the hole to the end of $O_3$.
--   2. Otherwise, writing $O_3=O_1'\mid T_2'O_2'\mid O_3'$: move $\min O_2'$ into the hole in $T_2$ using InsertMax; apply SwapHole $(O_2',T_2')$, transferring the hole to the end of $T_2'$; and invoke JumpDown $(i-1)$ on $O_3$.
--
--   If rebuilding has already moved the hole to the end of $S$ or of an enclosing section, the remaining steps are skipped.
--
--   **Formalization Note** The operation acts on the section at an address of a level-$d$ root, so that ReBuild may replace sections around it; it is defined by recursion on $i$.
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), §4.5.1, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_DynSort_insertMax
import Definitions.Def_DynSort_swapHole

namespace DynSort

/-! # JumpDown

Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.5.1, p.16 (PDF p.18).

For a three-block section `S = O₁ | T₂ O₂ | O₃` with the hole at the end of `T₂` (p.16):
"1. If O3 is a level-1 DST, move min O3 into the hole in T2 using InsertMax, and shift the elements
of O3 one position to the left to move the hole to the end of O3.
2. Otherwise, we perform the following steps:
(a) Move min O′2 into the hole in T2 using InsertMax.
(b) Apply SwapHole (O′2, T′2) from right to left, transferring the hole to the end of T′2.
(c) Invoke JumpDown (i − 1) on O3, moving the hole to the end of S.
As in all operations, if rebuilding has already moved the hole to the end of S or an enclosing
section, the corresponding unfinished operations terminate."

**Formalization Note.** `jumpDown d i a st` acts on the level-`i` section at address `a` of the
level-`d` root of `st`; it is structural in `i`. After step (b) it stops when `done` holds (the
Remark of p.15), and otherwise recurses on `O₃ = O′₁ | T′₂ O′₂ | O′₃`, read again from the root.
On a section that is not three-block, or whose `T₂` does not end with the hole, nothing happens.
-/

variable {α : Type}

/-- **JumpDown (i)** on the section at address `a` of a level-`d` root (p.16). -/
def jumpDown [LinearOrder α] (d : ℕ) : ℕ → List ℕ → St α → St α
  | 0, _, st => st
  | i + 1, a, st =>
    match st.root.get a with
    | some (.three _ T2 _ O3) =>
      if !T2.endsInHole then st
      else
        match O3 with
        | .leaf _ => shiftToEnd (a ++ [3]) (insertMax (a ++ [3]) (a ++ [1]) st)
        | .three .. =>
          let st1 := insertMax (a ++ [3, 2]) (a ++ [1]) st
          let st2 := swapHole d (a ++ [3, 2]) (a ++ [3, 1]) st1
          if done st2.root a then st2
          else
            match st2.root.get (a ++ [3]) with
            | some (.three _ T2' _ _) =>
              if T2'.endsInHole then jumpDown d i (a ++ [3]) st2 else st2
            | _ => st2
        | .single _ => st
    | _ => st

end DynSort



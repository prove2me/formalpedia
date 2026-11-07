-- Prove2me | Definitions.Def_DynSort_start2End
-- name    : DynSort_start2End
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:37:31.295219+00:00
-- url     : https://prove2.me/theorems/28875a3c-ea7d-4395-bedd-3ee394940f3c
-- title:
--   The Start2End operation
-- statement:
--   **Start2End $(i)$** moves a hole from the first to the last cell of a level-$i$ section $S$:
--
--   1. If $i=1$, shift the elements of the sorted array.
--   2. If $S$ is a single block with original section $O$, apply Start2End $(i-1)$ to $O$.
--   3. If $S=O_1\mid T_2O_2\mid O_3$ is not the last original section of a three-block parent, apply SimpleStart2End $(i)$ to $S$.
--   4. Otherwise $S$ is the last original section of $\hat S=\hat O_1\mid\hat T_2\hat O_2\mid S$. Apply SimpleStart2End $(i-1)$ to $O_1$. If $\hat T_2$ stores no element, move $\min O_2$ into the hole using InsertMax; otherwise move $\min\hat T_2$ into $O_1$, apply SimpleStart2End $(i)$ to $\hat T_2$, and move $\min O_2$ into the resulting hole in $\hat T_2$. Then apply SwapHole $(O_2,T_2)$ and JumpDown $(i)$.
--
--   Each step is skipped once rebuilding has moved the hole to the end of $S$ or of an enclosing section. The steps after the first are also used by Any2End when the hole is in $O_1$.
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), §4.5.2, pp.18–19 (PDF pp.20–21)

import Mathlib
import Definitions.Def_DynSort_simpleStart2End

namespace DynSort

/-! # Start2End

Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.5.2, pp.18–19 (PDF pp.20–21).

Verbatim (pp.18–19): "1. If i = 1, shift the elements of the sorted array to move the hole to its
last position. 2. If S contains a single block with original section O, call Start2End (i − 1) on
O. 3. Otherwise, S = O1 | T2 | O2 | O3 is a three-block DST. If S is not the last original section
of a three-block parent, call SimpleStart2End (i) on S. 4. Otherwise, S = Ô3 is the last original
section of a three-block parent Ŝ = Ô1 | T̂2 | Ô2 | S. In this case, we have the following steps:
(a) Apply SimpleStart2End (i − 1) to O1, moving the hole to the end of O1. […]
(b) We have two cases: i. If T̂2 is empty, we move min O2 to the hole using InsertMax.
ii. Otherwise, T̂2 is non-empty. In this case, we do the following: A. move min T̂2 into O1 using
InsertMax. B. apply SimpleStart2End (i) to T̂2. C. move the minimum element in O2 into the
resulting hole in T̂2, using InsertMax.
(c) Apply SwapHole (O2, T2) from right to left, moving the hole to the end of T2.
(d) Finally, apply JumpDown (i) to move the hole to the end of S.
As usual, if rebuilding has already moved the hole to the end of S or an enclosing section, the
corresponding unfinished operations terminate."

**Formalization Note.** `finishFromO1 d i a` performs steps 4(b)–(d) for the level-`i` section at
address `a` once the hole is at the end of its `O₁`; Any2End (case `A = O₁`, p.21) reuses it, with
Case 1 exactly when the section is the last original section (index 3) of a three-block parent
whose transfer section `T̂₂` (address `parent ++ [1]`) stores an element. `start2End d i a` is
structural in `i`; `T̂₂` has the same level `i` as `S`.
-/

variable {α : Type}

/-- Steps (b)–(d) of Start2End (p.18) for the level-`i` section at address `a`, with the hole at
the end of its first original section. -/
def finishFromO1 [LinearOrder α] (d i : ℕ) (a : List ℕ) (st : St α) : St α :=
  let p := a.dropLast
  let case1 : Bool := decide (a.getLast? = some 3) &&
    (match st.root.get (p ++ [1]) with
     | some T => !T.stored.isEmpty
     | none => false)
  let finish : St α → St α := fun st' =>
    let st'' := swapHole d (a ++ [2]) (a ++ [1]) st'
    if done st''.root a then st'' else jumpDown d i a st''
  if case1 then
    let st1 := insertMax (p ++ [1]) (a ++ [0]) st
    let st2 := simpleStart2End d i (p ++ [1]) st1
    if done st2.root a then st2
    else finish (insertMax (a ++ [2]) (p ++ [1]) st2)
  else finish (insertMax (a ++ [2]) (a ++ [0]) st)

/-- **Start2End (i)** on the section at address `a` of a level-`d` root (pp.18–19). -/
def start2End [LinearOrder α] (d : ℕ) : ℕ → List ℕ → St α → St α
  | 0, _, st => st
  | i + 1, a, st =>
    match st.root.get a with
    | some (.leaf _) => shiftToEnd a st
    | some (.single _) => start2End d i (a ++ [0]) st
    | some (.three ..) =>
      if a.getLast? ≠ some 3 then simpleStart2End d (i + 1) a st
      else
        let st1 := simpleStart2End d i (a ++ [0]) st
        if done st1.root a then st1 else finishFromO1 d (i + 1) a st1
    | none => st

end DynSort



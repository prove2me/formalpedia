-- Prove2me | Definitions.Def_DynSort_any2End
-- name    : DynSort_any2End
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:38:38.492191+00:00
-- url     : https://prove2.me/theorems/d732e5fe-8650-4f44-8e2f-7c37508c47ee
-- title:
--   The Any2End operation
-- statement:
--   **Any2End $(i)$** moves a hole from an arbitrary cell to the last cell of a level-$i$ section $S$:
--
--   1. If $i=1$, shift the elements following the hole one position to the left.
--   2. If $S$ is a single block with original section $O$, apply Any2End $(i-1)$ to $O$.
--   3. Otherwise, writing $S=O_1\mid T_2O_2\mid O_3$, let $A$ be the section holding the hole and apply Any2End $(i-1)$ to $A$. Then: if $A=O_3$, stop; if $A=T_2$, apply JumpDown $(i)$; if $A=O_2$ and $T_2$ is nonempty with $\min T_2<\min O_3$, move $\min T_2$ into the hole, apply SimpleStart2End $(i-1)$ to $T_2$ and JumpDown $(i)$, and otherwise move $\min O_3$ into the hole and apply Start2End $(i-1)$ to $O_3$; if $A=O_1$, continue as Start2End does after its first step.
--
--   Each step is skipped once rebuilding has moved the hole to the end of $S$ or of an enclosing section.
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), §4.5.2, pp.20–21 (PDF pp.22–23)

import Mathlib
import Definitions.Def_DynSort_start2End

namespace DynSort

/-! # Any2End

Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.5.2, pp.20–21 (PDF pp.22–23).

Verbatim (pp.20–21): "1. If i = 1, shift the elements following the hole one position to the left.
2. If the DST contains a single block with original section O, call Any2End (i − 1) on O.
3. Otherwise, write S = O1 | T2 | O2 | O3. Let A denote the section containing the hole. First,
call Any2End (i − 1) on A. We now have the following cases:
(a) If A = O3, we end the operation. (b) If A = T2, call JumpDown (i).
(c) If A = O2, we distinguish two cases. i. If T2 is nonempty and min T2 < min O3 (may only happen
when O3 is a level-1 section), move min T2 into the hole using InsertMax, apply SimpleStart2End
(i − 1) to T2, and invoke JumpDown (i). ii. Otherwise, move min O3 into the hole and apply
Start2End (i − 1) to O3.
(d) If A = O1, we proceed as follows: i. […] Case 1: If S is the last original section of a
three-block parent Ŝ = Ô1 | T̂2 | Ô2 | S, and T̂2 is nonempty, then we: A. Move min T̂2 into the
hole in O1 using InsertMax. B. Apply SimpleStart2End (i) to T̂2. C. Move min O2 into the resulting
hole in T̂2 using InsertMax. Case 2: Otherwise, we move min O2 into the hole in O1 using InsertMax.
ii. Apply SwapHole (O2, T2) from right to left, moving the hole to the end of T2.
iii. Finally, apply JumpDown (i) to move the hole to the end of S."

**Formalization Note.** `any2End d i a` is structural in `i`. `A` is the first child holding the
hole; the comparison `min T₂ < min O₃` is on the stored elements (`List.min?`), and is false when
`O₃` stores nothing. Case (d) is `finishFromO1`. Each step after a sub-call is truncated by `done`.
-/

variable {α : Type}

/-- **Any2End (i)** on the section at address `a` of a level-`d` root (pp.20–21). -/
def any2End [LinearOrder α] (d : ℕ) : ℕ → List ℕ → St α → St α
  | 0, _, st => st
  | i + 1, a, st =>
    match st.root.get a with
    | some (.leaf _) => shiftToEnd a st
    | some (.single _) => any2End d i (a ++ [0]) st
    | some (.three O1 T2 O2 O3) =>
      match [O1, T2, O2, O3].findIdx? (fun X => decide (X.holes ≠ 0)) with
      | none => st
      | some k =>
        let st1 := any2End d i (a ++ [k]) st
        if done st1.root a then st1
        else
          match k with
          | 3 => st1
          | 1 => jumpDown d (i + 1) a st1
          | 2 =>
            match st1.root.get a with
            | some (.three _ T2n _ O3n) =>
              let smallT : Bool :=
                match T2n.stored.min?, O3n.stored.min? with
                | some t, some o => decide (t < o)
                | _, _ => false
              if smallT then
                let st2 := insertMax (a ++ [1]) (a ++ [2]) st1
                let st3 := simpleStart2End d i (a ++ [1]) st2
                if done st3.root a then st3 else jumpDown d (i + 1) a st3
              else start2End d i (a ++ [3]) (insertMax (a ++ [3]) (a ++ [2]) st1)
            | _ => st1
          | _ => finishFromO1 d (i + 1) a st1
    | none => st

end DynSort



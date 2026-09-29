-- Prove2me | Definitions.Def_FiniteMagmaE677_seventh_element_growth
-- name    : FiniteMagmaE677_seventh_element_growth
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-23T20:29:23.129105+00:00
-- url     : https://prove2.me/theorems/397631da-a704-4340-a4de-9eca96f84c4d
-- title:
--   Period-four named-element growth packet
-- statement:
--   This interface records the named elements used in one step of the period-four E677 collision argument. Write $q=c_2\diamond x$, $r=c_1\diamond c_2$, and $s=c_3\diamond q$.
--
--   The freshness predicate says that a candidate differs from each of six listed elements. The growth packet records the q-collision, both q-packet equations, exclusion of q from the four base points, and either the R branch with a fresh $L_x(q)$ or $L_x(r)$, or the S branch with a fresh $L_x(q)$, $L_x(s)$ or $c_2\diamond s$.
--
--   This packet accompanies a displayed four-cycle of pairwise distinct base points. Those cycle and distinctness assumptions are supplied by the theorem that produces it; they are not asserted by the packet definition alone.
-- source:
--   Adam McKenna, The Missing Pair, revision 9b76827c2246f0e6288466768f15b5c6f9350d71; Piece1D4SeventhElementGrowth.lean, e677_minimalPeriodFour_orbitRightCollision_hasFixer_or_seventhElementGrowth; R/S branch algebra in Piece1D4RBranchGrowth.lean and Piece1D4SBranchGrowth.lean. https://github.com/flound1129/the-missing-pair/blob/9b76827c2246f0e6288466768f15b5c6f9350d71/lean/E677/Spine/Piece1D4SeventhElementGrowth.lean

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_FiniteMagmaE677

/-!
# D4 seventh-element source growth

Definitions for the branch-preserving strict six-to-seven source-term
conclusion attached to the period-four q packet.
-/

universe u

namespace FiniteMagmaE677

/-! A source term outside six named elements of a distinguished D4 branch. -/
set_option linter.unusedVariables false in
def FreshOutsideSix {α : Type u} (op : α → α → α)
    (x c1 c2 c3 q s t : α) : Prop :=
  t ≠ x ∧ t ≠ c1 ∧ t ≠ c2 ∧ t ≠ c3 ∧ t ≠ q ∧ t ≠ s

/-! The branch-preserving strict `6 → 7` conclusion for the D4 q packet.

The first branch retains `r = c₁ ◇ c₂`; the second retains `r = c₁` and
`s = c₃ ◇ q`.  The final disjunction displays the source term witnessing
strict growth in each branch. -/
def SeventhElementGrowth {α : Type u} (op : α → α → α)
    (x c1 c2 c3 : α) : Prop :=
  (op c2 x = op c3 x ∧
    op c1 (op c2 x) = x ∧
    op c2 (op c2 x) = c1 ∧
    op c2 x ≠ x ∧
    op c2 x ≠ c1 ∧
    op c2 x ≠ c2 ∧
    op c2 x ≠ c3 ∧
    (((op c1 c2 ≠ x ∧
        op c1 c2 ≠ c1 ∧
        op c1 c2 ≠ c2 ∧
        op c1 c2 ≠ c3 ∧
        op c1 c2 ≠ op c2 x) ∧
      (FreshOutsideSix op x c1 c2 c3 (op c2 x) (op c1 c2)
          (op x (op c2 x)) ∨
        FreshOutsideSix op x c1 c2 c3 (op c2 x) (op c1 c2)
          (op x (op c1 c2)))) ∨
    ((op c1 c2 = c1 ∧
        op c3 (op c2 x) ≠ x ∧
        op c3 (op c2 x) ≠ c1 ∧
        op c3 (op c2 x) ≠ c2 ∧
        op c3 (op c2 x) ≠ c3 ∧
        op c3 (op c2 x) ≠ op c2 x) ∧
      (FreshOutsideSix op x c1 c2 c3 (op c2 x) (op c3 (op c2 x))
          (op x (op c2 x)) ∨
        FreshOutsideSix op x c1 c2 c3 (op c2 x) (op c3 (op c2 x))
          (op x (op c3 (op c2 x))) ∨
        FreshOutsideSix op x c1 c2 c3 (op c2 x) (op c3 (op c2 x))
          (op c2 (op c3 (op c2 x)))))))

end FiniteMagmaE677



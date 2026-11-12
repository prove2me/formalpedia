-- Prove2me | Definitions.Def_RobotMP_W1Hard_ReferenceCenters
-- name    : RobotMP_W1Hard_ReferenceCenters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:41:54.438613+00:00
-- url     : https://prove2.me/theorems/2a9d363d-0e89-4675-a103-b3487c640d42
-- title:
--   Reference centers on the even-integer grid (§10)
-- statement:
--   The **reference centers** are the closed $1 \times 1$ squares
--   $$C_{a,b} = [2a, 2a+1] \times [2b, 2b+1], \qquad (a, b) \in \mathbb Z^2,$$
--   whose lower-left corners lie on the even-integer grid. A set $P \subseteq \mathbb R^2$ **cuts no reference center** if every $C_{a,b}$ either lies inside $P$ or is disjoint from $P$. The reference centers in $P$ are those with $C_{a,b} \subseteq P$.
--
--   In the paper's reduction, the polygon is built to cut no reference center, and packings with as many unit squares (side length $2$) as reference centers are analysed through them.
-- source:
--   Agarwal, Holmgren, Stade, Near-Optimal Makespan and Parameterized Hardness for Multi-Robot Motion Planning, STOC 2027 submission (manuscript sha256 17b4fe59…), pp. 54–56, §10 (reference centers)

import Mathlib
import Definitions.Def_UnitSquarePack_NPHard_Squares

set_option autoImplicit false

namespace RobotMP.W1Hard

open Set

/-- The reference center with index `(a, b) ∈ ℤ²` (§10, p. 54): the closed `1 × 1` square
`[2a, 2a + 1] × [2b, 2b + 1]`, whose lower-left corner lies on the even-integer grid. -/
def refCenter (ab : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Icc (2 * (ab.1 : ℝ)) (2 * (ab.1 : ℝ) + 1) ×ˢ Icc (2 * (ab.2 : ℝ)) (2 * (ab.2 : ℝ) + 1)

/-- The union of all reference centers. -/
def refCenters : Set (ℝ × ℝ) :=
  ⋃ ab : ℤ × ℤ, refCenter ab

/-- `P` cuts no reference center: each reference center lies entirely inside `P` or is disjoint
from `P`. -/
def CutsNoRefCenter (P : Set (ℝ × ℝ)) : Prop :=
  ∀ ab : ℤ × ℤ, refCenter ab ⊆ P ∨ Disjoint (refCenter ab) P

/-- The indices of the reference centers contained in `P`. -/
def refCentersIn (P : Set (ℝ × ℝ)) : Set (ℤ × ℤ) :=
  {ab | refCenter ab ⊆ P}

end RobotMP.W1Hard



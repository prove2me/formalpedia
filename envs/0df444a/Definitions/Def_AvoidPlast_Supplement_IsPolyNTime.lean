-- Prove2me | Definitions.Def_AvoidPlast_Supplement_IsPolyNTime
-- name    : AvoidPlast_Supplement_IsPolyNTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:57:29.896145+00:00
-- url     : https://prove2.me/theorems/d44e497a-fccd-42f3-b549-176d34f2cec1
-- title:
--   Non-deterministic polynomial-time machines
-- statement:
--   A non-deterministic polynomial-time machine is a deterministic machine with read-only tapes for the input $x$ and a witness $w$ that halts within $a(|x|^a+1)$ steps for every $x$ and every $w$. Rejection on a witness is the output $\bot$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 3.5, p.14; Sections 6–7

import Mathlib
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Machine

namespace AvoidPlast.Supplement

open AvoidPlast

/-- A non-deterministic polynomial-time machine (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 3.5, p.14; Theorems 6.1,
6.5–6.11, 7.2, 7.3): a deterministic machine with read-only tapes for the input `x` and the
witness `w` that halts within `a(|x|^a + 1)` steps for every `x` and `w`. -/
def IsPolyNTime (A : Machine 2) (a : ℕ) : Prop :=
  ∀ x w : List Bool, HaltsWithin A ![x, w] (a * (x.length ^ a + 1))

end AvoidPlast.Supplement



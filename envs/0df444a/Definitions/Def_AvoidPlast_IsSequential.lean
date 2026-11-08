-- Prove2me | Definitions.Def_AvoidPlast_IsSequential
-- name    : AvoidPlast_IsSequential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:54.310213+00:00
-- url     : https://prove2.me/theorems/6e32d085-b4a1-41b1-bea3-e5174c845dea
-- title:
--   Multitape Turing machines
-- statement:
--   A *multitape Turing machine* in the sense of footnote 17 of the paper is a machine whose transition function never issues a jump.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 4.2, footnote 17, p.17

import Mathlib
import Definitions.Def_AvoidPlast_HeadAct
import Definitions.Def_AvoidPlast_Machine

namespace AvoidPlast

/-- A *multitape Turing machine* (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), footnote 17, p.17): a machine whose transition function
never issues a jump. -/
def IsSequential {r : ℕ} (M : Machine r) : Prop :=
  ∀ s a b j, (M.δ s a b).2.2.1 j ≠ HeadAct.jump

end AvoidPlast



-- Prove2me | Definitions.Def_AvoidPlast_moveApply
-- name    : AvoidPlast_moveApply
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:57.043607+00:00
-- url     : https://prove2.me/theorems/f63dc136-a0d3-48a4-8a20-0308db2c6f6b
-- title:
--   Effect of a head move
-- statement:
--   The effect of a move on a head position $p$: $p\mapsto p-1$ (with $0\mapsto 0$), $p\mapsto p$, $p\mapsto p+1$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3, machine model, p.13

import Mathlib
import Definitions.Def_AvoidPlast_Move

namespace AvoidPlast

/-- The effect of a head move on a head position (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3, p.13, the machine model).
A left move on cell `0` stays on cell `0`. -/
def moveApply : Move → ℕ → ℕ
  | Move.left, p => p - 1
  | Move.stay, p => p
  | Move.right, p => p + 1

end AvoidPlast



-- Prove2me | Definitions.Def_AvoidPlast_HeadAct
-- name    : AvoidPlast_HeadAct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:55.742382+00:00
-- url     : https://prove2.me/theorems/1b507c78-d01c-4c21-9238-951ea2aae637
-- title:
--   Actions of a read-only head
-- statement:
--   In one step a read-only input head either makes an ordinary head move or *jumps* to the cell whose index is written in binary on the head's index tape. Jumps give random access to the input, which is what the paper's RAM model provides and what makes sublinear time meaningful.
--
--   **Formalization Note** A machine that never jumps is an ordinary multitape Turing machine.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3, machine model, p.13

import Mathlib
import Definitions.Def_AvoidPlast_Move

namespace AvoidPlast

/-- The action of a read-only input head in one step (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3, p.13, the machine model): either
an ordinary head move, or a *jump* to the cell whose index is written in binary on the head's
index tape.

**Formalization Note** Jumps make read-only input tapes random-access, which is the paper's RAM
model ("The machine model throughout the paper is the RAM model", p.13). A machine that never
jumps is an ordinary multitape Turing machine (`IsSequential`). -/
inductive HeadAct
  | move (m : Move)
  | jump
  deriving DecidableEq, Encodable

end AvoidPlast



-- Prove2me | Definitions.Def_AvoidPlast_encodeMachine
-- name    : AvoidPlast_encodeMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:33.029832+00:00
-- url     : https://prove2.me/theorems/a656dd8c-0229-400a-8018-9c4a297a8085
-- title:
--   Machine codes
-- statement:
--   The binary code of a machine: the binary digits of its fixed `Encodable` code.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 5.13, p.29

import Mathlib
import Definitions.Def_AvoidPlast_Machine

namespace AvoidPlast

/-- The binary code of a machine (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 5.13, p.29, machine descriptions, reading R4):
the binary digits of its `Encodable` code. -/
def encodeMachine (M : Machine 1) : List Bool :=
  Nat.bits (Encodable.encode M)

end AvoidPlast



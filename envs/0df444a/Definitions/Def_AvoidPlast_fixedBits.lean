-- Prove2me | Definitions.Def_AvoidPlast_fixedBits
-- name    : AvoidPlast_fixedBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:43.173215+00:00
-- url     : https://prove2.me/theorems/c3f755e5-00cc-4a6d-a782-9ca1ef2dddc2
-- title:
--   Fixed-width binary codes
-- statement:
--   The $w$-bit binary code of a number, least significant bit first, used to write field elements in truth tables.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 4.5, p.18

import Mathlib

namespace AvoidPlast

/-- The `w`-bit binary code of a number, least significant bit first (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 4.5, p.18, field
elements in a truth table). -/
def fixedBits (w n : ℕ) : List Bool :=
  (List.range w).map (Nat.testBit n)

end AvoidPlast



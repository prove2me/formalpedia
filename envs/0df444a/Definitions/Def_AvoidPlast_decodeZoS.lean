-- Prove2me | Definitions.Def_AvoidPlast_decodeZoS
-- name    : AvoidPlast_decodeZoS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:20.75953+00:00
-- url     : https://prove2.me/theorems/4418757a-5e93-4e80-9de5-79cf7b2df6a1
-- title:
--   Decoding the explicit input
-- statement:
--   The tuple $(|F|,m,d,|H|)$ written in an explicit input, if the string is the code of one. Such a tuple is unique since the code is injective.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 4.5, p.18

import Mathlib
import Definitions.Def_AvoidPlast_encZoS

namespace AvoidPlast

open Classical in
/-- The tuple `(|F|, m, d, |H|)` written in an explicit input, if it is the code of one (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728),
Theorem 4.5, p.18). `encZoS` is injective, so the tuple is unique. -/
noncomputable def decodeZoS (x : List Bool) : Option (ℕ × ℕ × ℕ × ℕ) :=
  if h : ∃ p : ℕ × ℕ × ℕ × ℕ, encZoS p.1 p.2.1 p.2.2.1 p.2.2.2 = x then some h.choose else none

end AvoidPlast



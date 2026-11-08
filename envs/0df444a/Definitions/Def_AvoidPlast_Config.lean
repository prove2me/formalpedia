-- Prove2me | Definitions.Def_AvoidPlast_Config
-- name    : AvoidPlast_Config
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:43.552107+00:00
-- url     : https://prove2.me/theorems/9f6fbad4-1ff7-468c-a50d-5cc14911d4fe
-- title:
--   Machine configurations
-- statement:
--   A configuration records the state, the contents and head positions of the work tapes, the head positions of the read-only tapes, and the bits written so far on the output tape.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3, machine model, p.13

import Mathlib
import Definitions.Def_AvoidPlast_Machine

namespace AvoidPlast

/-- A configuration of a machine (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3, p.13, the machine model): the state, the contents and
head positions of the work tapes, the head positions of the read-only tapes, and the bits written
so far on the write-only output tape. -/
structure Config {r : ℕ} (M : Machine r) where
  /-- the current state -/
  state : Fin (M.q + 1)
  /-- the contents of the work tapes -/
  work : Fin (M.w + r) → ℕ → Option Bool
  /-- the head positions on the work tapes -/
  workPos : Fin (M.w + r) → ℕ
  /-- the head positions on the read-only tapes -/
  inPos : Fin r → ℕ
  /-- the output tape, in writing order -/
  out : List Bool

end AvoidPlast



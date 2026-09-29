-- Prove2me | Definitions.Def_ZZ_ProbeB
-- name    : ZZ_ProbeB
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-26T13:36:21.579815+00:00
-- url     : https://prove2.me/theorems/a2ab713d-92b6-43f0-bf2d-a3147206ff8c
-- title:
--   probe B
-- statement:
--   probe

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

def leftRegion (n : ℕ) : Set ℂ :=
  {z : ℂ | z.re < (n : ℝ) + 1 ∧ ∀ j : Fin (n + 1), z ≠ ((j : ℕ) + 1 : ℂ)}

theorem leftRegion_mem_iff (n : ℕ) (z : ℂ) :
    z ∈ leftRegion n ↔
      z.re < (n : ℝ) + 1 ∧ (∀ j : Fin (n + 1), z ≠ ((j : ℕ) + 1 : ℂ)) := by
  show z ∈ ({w : ℂ | w.re < (n : ℝ) + 1 ∧
      ∀ j : Fin (n + 1), w ≠ ((j : ℕ) + 1 : ℂ)} : Set ℂ) ↔ _
  rfl

end BraidsLinksMCG



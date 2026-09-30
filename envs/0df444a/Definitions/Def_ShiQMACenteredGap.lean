-- Prove2me | Definitions.Def_ShiQMACenteredGap
-- name    : ShiQMACenteredGap
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-30T06:56:09.770369+00:00
-- url     : https://prove2.me/theorems/d07acf82-6a73-4f19-89e2-106040bcc331
-- title:
--   Centered acceptance-bias iteration for majority-of-three QMA amplification
-- statement:
--   Defines the centered majority-of-three bias map $d\mapsto3d/2-2d^3$, its iteration, and a logarithmic schedule for turning an inverse-polynomial acceptance bias into a constant. Separate theorem nodes prove the growth and copy-count guarantees.
-- source:
--   Yueheng Shi, AMPUNI-centered-gap.lean, formal bias analysis for copy-based QMA amplification; context: Marriott and Watrous, Quantum Arthur–Merlin Games (2005), Section 3, Theorem 3, https://cs.uwaterloo.ca/~watrous/Papers/QuantumArthurMerlinGames.pdf

import Definitions.Def_ShiQMAErrorIteration
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace ShiQMACenteredGap
open ShiQMAErrorIteration

/-- Majority of three acts on displacement from acceptance probability one half. -/
noncomputable def biasStep (d : ℝ) : ℝ := 3 / 2 * d - 2 * d ^ 3

noncomputable def biasIter (d : ℝ) : Nat → ℝ
  | 0 => d
  | r + 1 => biasStep (biasIter d r)

/-- A concrete logarithmic schedule for a bias at least 1/(6q). -/
def gapRounds (q : Nat) : Nat := 3 * (Nat.log 2 q + 1)

end ShiQMACenteredGap



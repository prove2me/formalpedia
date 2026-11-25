-- Prove2me | Definitions.Def_DetDLP_D3StoppedSchedule
-- name    : DetDLP_D3StoppedSchedule
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:27:29.424748+00:00
-- url     : https://prove2.me/theorems/09e49274-10de-4800-9987-83548c1d1e25
-- title:
--   Absolute continuation schedule for a stopped core
-- statement:
--   The schedule keeps the creation depth and global scale. A direct-sum leaf has zero further levels; otherwise the suffix ends when the worst-case mass reaches the core threshold. Its widths and cumulative shifts are indexed by absolute depth.
-- source:
--   Deterministic Discrete Logarithms, Lemma 5.3(iii).

import Definitions.Def_DetDLP_OpenAIAppendixD

set_option autoImplicit false
namespace DetDLP.D3Stopped
open AppendixD4
noncomputable section

def level (S : ℕ) := Nat.clog 2 S
def threshold (S : ℕ) := (S + (level S).sqrt - 1) / max 1 (level S).sqrt
def width (S j : ℕ) := (level S / 131072) / 2^j
def shift (S j : ℕ) := 2 * ∑ t ∈ Finset.range (j+1), width S t
/-- A computable dyadic majorant of the degree cap, using ceiling log rather than real powers. -/
def cap (S : ℕ) := 2^((9*level S+9)/10)
/-- The suffix ends once the worst possible remaining mass is below the direct-sum threshold. -/
def depth (C S : ℕ) := Nat.clog 8 (C * max 1 (level S).sqrt)

def schedule (C S M d₀ : ℕ) : Schedule where
  H := min M (threshold S)
  start := d₀
  D := if M ≤ threshold S then 0 else depth C S - d₀
  cap := cap S
  u j := width S (d₀+j.val)
  a j := shift S (d₀+j.val)
  κ := 4 * level S

end
end DetDLP.D3Stopped



-- Prove2me | Definitions.Def_BMO5Adm
-- name    : BMO5Adm
-- status  : Definition
-- author  : @alon yuval
-- created : 2026-11-23T17:24:32.863832+00:00
-- url     : https://prove2.me/theorems/4582ff00-3bdf-41c5-b65a-49adb7a7b84e
-- title:
--   BMO #5: admissible halting levels via backward T/ST blocks
-- statement:
--   Write $N_i = 20\cdot 2^i + i + 1$ (the halting value of $c = 2b + a + 5$ at level $i$). $\mathrm{adm}(D, i)$ holds iff there is a sequence of $D$ backward blocks, each either *T* (undo a tripling) or *ST* (undo a subtraction from level $i - \delta - 1$, then a tripling), such that every undone tripling is integral. In formulas: starting from $F = N_i$, $m = \delta = 0$, block T needs $3^{m+1} \mid F$; block ST replaces $F$ by $F + 3^m(20\cdot 2^{i-\delta-1} - 3)$, increments $\delta$, and needs $3^{m+1} \mid F$; each block increments $m$.
-- source:
--   Beaver Math Olympiad problem 5 (machine 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE), https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad. Original result of this submission; builds on BMO5.level_halt_dvd, BMO5.three_adic_uniqueness, BMO5.halt_level_mod18.

import Mathlib

namespace BMO5Adm

/-- Backward block check for BMO #5 (see natural-language statement). -/
def okb (i : ℕ) : ℕ → ℤ → ℕ → ℕ → Bool
  | 0, _, _, _ => true
  | D + 1, F, m, d =>
    (F % 3 ^ (m + 1) == 0 && okb i D F (m + 1) d) ||
      ((F + 3 ^ m * (20 * 2 ^ (i - d - 1) - 3)) % 3 ^ (m + 1) == 0 &&
        okb i D (F + 3 ^ m * (20 * 2 ^ (i - d - 1) - 3)) (m + 1) (d + 1))

/-- `adm D i`: a halt at level `i` is compatible with `D` backward blocks. -/
def adm (D i : ℕ) : Bool := okb i D (20 * 2 ^ i + (i : ℤ) + 1) 0 0

end BMO5Adm



-- Prove2me | Definitions.Def_CarryRNG_SWB_out
-- name    : CarryRNG_SWB_out
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:44.485849+00:00
-- url     : https://prove2.me/theorems/81ce1883-1cd7-4723-954a-fd7fb84ffd24
-- title:
--   The generated digit stream
-- statement:
--   Starting from a state $(x_1,\ldots,x_r,c)$, the one-based output stream begins with the seed digits and then records the digit appended at each iteration:
--   $$x_1,\ldots,x_r,x_{r+1},x_{r+2},\ldots.$$
--   For $n=r+j$ with $j\ge1$, $x_n$ is the last digit of the state after $j$ steps. Lean index zero is the paper’s $x_1$. The function’s value at $n=0$ is outside this one-based convention and is unused.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), pp. 466–467, Sections 3–4

import Definitions.Def_CarryRNG_SWB_step

namespace CarryRNG.SWB

/-- The one-based stream: seed digits first, then the new last CarryRNG.AWC.digit after each step. -/
def out (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b) (z : CarryRNG.AWC.State b L.r) (n : ℕ) : ℕ :=
  if h : 1 ≤ n ∧ n ≤ L.r then (z.x ⟨n - 1, by omega⟩).val
  else (((step b L hb)^[n - L.r] z).x ⟨L.r - 1, by have := L.hsr; omega⟩).val

end CarryRNG.SWB



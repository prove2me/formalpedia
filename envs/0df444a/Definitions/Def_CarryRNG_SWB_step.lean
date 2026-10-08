-- Prove2me | Definitions.Def_CarryRNG_SWB_step
-- name    : CarryRNG_SWB_step
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:29.013001+00:00
-- url     : https://prove2.me/theorems/d0f6a8f3-7b01-4516-935b-ba214b494e2a
-- title:
--   Method 1 subtract-with-borrow step
-- statement:
--   For base $b\ge2$, lags $0<s<r$, and state $(x_1,\ldots,x_r,c)$, put $t=x_{r+1-s}-x_1-c$. One step discards $x_1$, shifts the remaining digits left, and appends
--   $$
--   (x_{r+1},c')=\begin{cases}(t,0),&t\ge0,\\(t+b,1),&t<0.\end{cases}
--   $$
--   This is Method 1, with recurrence $x_n=x_{n-s}-x_{n-r}-c$ modulo $b$. The subtraction is evaluated as an integer before the borrow branch. Lean index $r-s$ denotes the paper’s $x_{r+1-s}$.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 466, Section 3

import Definitions.Def_CarryRNG_AWC_State

namespace CarryRNG.SWB

/-- Method 1 of Section 3: shift the digits and append
`x_(r+1-s) - x_1 - c` modulo `b`, borrowing exactly when negative. -/
def step (b : ℕ) (L : CarryRNG.AWC.Lags) (_hb : 2 ≤ b) (z : CarryRNG.AWC.State b L.r) : CarryRNG.AWC.State b L.r := by
  have hs := L.hs
  have hsr := L.hsr
  let a : ℕ := (z.x ⟨L.r - L.s, by omega⟩).val
  let d : ℕ := (z.x ⟨0, by omega⟩).val
  let borrow : Bool := a < d + z.c.val
  let newDigit : ℕ := if borrow then a + b - (d + z.c.val) else a - (d + z.c.val)
  refine ⟨fun i => if h : i.val + 1 < L.r then z.x ⟨i.val + 1, h⟩ else ⟨newDigit, ?_⟩,
    ⟨if borrow then 1 else 0, by split <;> omega⟩⟩
  have ha : a < b := (z.x ⟨L.r - L.s, by omega⟩).isLt
  have hd : d < b := (z.x ⟨0, by omega⟩).isLt
  have hc : z.c.val < 2 := z.c.isLt
  by_cases hborrow : a < d + z.c.val
  · simp [newDigit, borrow, hborrow]
    omega
  · simp [newDigit, borrow, hborrow]
    omega

end CarryRNG.SWB



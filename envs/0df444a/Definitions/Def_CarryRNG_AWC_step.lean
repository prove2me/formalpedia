-- Prove2me | Definitions.Def_CarryRNG_AWC_step
-- name    : CarryRNG_AWC_step
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:35.67329+00:00
-- url     : https://prove2.me/theorems/ecf11160-c647-494d-bc22-b5e9627b21a4
-- title:
--   The add-with-carry map $f$ (Section 2, p. 465)
-- statement:
--   Let $b$ be a base and $0 < s < r$ lags. The **add-with-carry map** $f$ sends a state $(x_1, \dots, x_r, c)$ to
--
--   $$
--   f(x_1, \dots, x_r, c) =
--   \begin{cases}
--   (x_2, \dots, x_r,\ x_{r+1-s} + x_1 + c,\ 0) & \text{if } x_{r+1-s} + x_1 + c < b,\\
--   (x_2, \dots, x_r,\ x_{r+1-s} + x_1 + c - b,\ 1) & \text{if } x_{r+1-s} + x_1 + c \ge b.
--   \end{cases}
--   $$
--
--   The digits move one place to the left, the oldest digit $x_1$ is dropped, and the new last digit is $x_{r+1-s} + x_1 + c$ reduced by $b$ when it overflows, the overflow becoming the new carry. Since all digits are below $b$ and $c \le 1$, the sum is at most $2b - 1$, so the new last entry is again a digit. Written as a recurrence on the generated sequence, this is $x_n = x_{n-r} + x_{n-s} + c \bmod b$ (Section 4.2, p. 467). The **generated sequence** of a seed $x$ is $x, f(x), f^2(x), \dots$.
--
--   **Formalization Note** With the Lean index convention (index $i$ is the paper's $x_{i+1}$) the oldest digit $x_1$ is index $0$ and the partner digit $x_{r+1-s}$ is index $r - s$; the map is defined directly from the two-case formula above. No hypothesis on $b$ is needed for the definition: a state exists only if $b \ge 1$.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 465, Section 2, display defining f(x_1, ..., x_r, c)

import Definitions.Def_CarryRNG_AWC_State

namespace CarryRNG.AWC

/-- The add-with-carry map `f` of Section 2 (p. 465):
`f(x_1, …, x_r, c) = (x_2, …, x_r, x_{r+1-s} + x_1 + c, 0)` if `x_{r+1-s} + x_1 + c < b`, and
`(x_2, …, x_r, x_{r+1-s} + x_1 + c - b, 1)` otherwise.
The paper's `x_1` is Lean index `0` and `x_{r+1-s}` is Lean index `r - s`. -/
def step (b : ℕ) (L : Lags) (z : State b L.r) : State b L.r := by
  have hs := L.hs
  have hsr := L.hsr
  let x1 : ℕ := (z.x ⟨0, by omega⟩).val
  let xp : ℕ := (z.x ⟨L.r - L.s, by omega⟩).val
  let t : ℕ := xp + x1 + z.c.val
  refine ⟨fun i => if h : i.val + 1 < L.r then z.x ⟨i.val + 1, h⟩
      else (if ht : t < b then ⟨t, ht⟩ else ⟨t - b, ?_⟩),
    if t < b then 0 else 1⟩
  have h1 : x1 < b := (z.x ⟨0, by omega⟩).isLt
  have h2 : xp < b := (z.x ⟨L.r - L.s, by omega⟩).isLt
  have h3 : z.c.val < 2 := z.c.isLt
  omega

end CarryRNG.AWC



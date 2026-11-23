-- Prove2me | Definitions.Def_collatzMinPreimage
-- name    : collatzMinPreimage
-- status  : Definition
-- author  : @Siyuan Chen
-- created : 2026-11-23T15:11:29.155116+00:00
-- url     : https://prove2.me/theorems/aaa119fe-13c2-42a0-8bfc-859f9f4226f6
-- title:
--   Minimum preimage of the classical Collatz map at bounded depth
-- statement:
--   For a depth $d$ and a natural number $y$, take the least value in the backward Collatz tree through depth $d$. The root $y$ counts as a depth-zero node. Each node $x$ has the even predecessor $2x$ and has the odd predecessor $\lfloor x/3\rfloor$ exactly when $x$ is $4$ modulo $6$. The function is total on natural numbers, including zero.
-- source:
--   D. Applegate and J. C. Lagarias, Lower bounds for the total stopping time of 3X+1 iterates, Math. Comp. 72 (2003), Section 2 (inverse trees), https://arxiv.org/abs/math/0103054. This definition takes the minimum of the depth-bounded inverse tree for the classical, unaccelerated map.

/-- The smallest start that reaches `y` in at most `depth` classical Collatz steps.
The zero-step candidate is `y` itself. The one-step predecessors are the even number
`2 * y` and, when `y % 6 = 4`, the odd number `y / 3`. -/
def collatzMinPreimage : Nat → Nat → Nat
  | 0, y => y
  | depth + 1, y =>
    min y (min (collatzMinPreimage depth (2 * y))
      (if y % 6 = 4 then collatzMinPreimage depth (y / 3) else y))



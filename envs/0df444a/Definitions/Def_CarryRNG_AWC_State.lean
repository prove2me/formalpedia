-- Prove2me | Definitions.Def_CarryRNG_AWC_State
-- name    : CarryRNG_AWC_State
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:12:33.513413+00:00
-- url     : https://prove2.me/theorems/87bc1fd5-ba2d-4fa0-8bd5-774b014aca84
-- title:
--   Seed vectors $(x_1,\dots,x_r,c)$ of the carry generators (Sections 2–3)
-- statement:
--   Fix a base $b \ge 2$ and a lag $r$. A **state** (or **seed vector**) of either carry generator is a vector
--
--   $$x = (x_1, x_2, \dots, x_r, c)$$
--
--   whose first $r$ entries are base-$b$ digits, $x_i \in \{0, 1, \dots, b-1\}$, and whose last entry is a **carry bit** $c \in \{0, 1\}$. The digit $x_1$ is the oldest one: the generator drops it at the next step.
--
--   The set of states is finite, with $2b^r$ elements.
--
--   **Formalization Note** A state is a structure with a digit field `x : Fin r → Fin b` and a carry field `c : Fin 2`. Lean index `i : Fin r` stands for the paper's $x_{i+1}$, so `x 0` is $x_1$ and `x (r - 1)` is $x_r$. The carry type `Fin 2` makes $c \le 1$ hold by typing. The structure derives `DecidableEq` and `Fintype`. The type can be formed at other values of $b$ and $r$; generator theorems impose the paper's $b \ge 2$ and $0 < s < r$.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 465, Section 2 (seed vector x = (x_1, ..., x_r, c)); p. 466, Section 3 (c = 0 or 1)

import Definitions.Def_CarryRNG_AWC_Lags

namespace CarryRNG.AWC

/-- A state (seed vector) `(x_1, …, x_r, c)`: `r` base-`b` digits and a carry bit.
Lean index `i : Fin r` is the paper's `x_{i+1}`, so `x 0` is `x_1`, the oldest digit. -/
structure State (b r : ℕ) where
  x : Fin r → Fin b
  c : Fin 2
  deriving DecidableEq, Fintype

end CarryRNG.AWC



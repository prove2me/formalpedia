-- Prove2me | Definitions.Def_Nat_MacaulayPow
-- name    : Nat_MacaulayPow
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/0d6c2441-82b9-5cba-aa9d-bc350be56bb6
-- title:
--   Macaulay's upper pseudo-power of a natural number
-- statement:
--   This module defines a single arithmetic function, [`Nat.macaulayPow : ℕ → ℕ → ℕ`](../def/Nat_MacaulayPow.html#L7), written here as $a^{\langle d\rangle}$ for [`Nat.macaulayPow d a`](../def/Nat_MacaulayPow.html#L7): Macaulay's upper pseudo-power of a natural number $a$ in degree $d$. It is defined by recursion on the first argument. In degree $0$ the value is $0$ for every $a$. In degree $d+1$, one first forms $k =$ `Nat.findGreatest (fun k => k.choose (d+1) ≤ a) (a+d+1)`, that is the largest $k \le a+d+1$ with $\binom{k}{d+1} \le a$ (and $0$ if no such $k$ exists); the value is then
--   $$a^{\langle d+1\rangle} \;=\; \binom{k+1}{d+2} \;+\; \bigl(a - \tbinom{k}{d+1}\bigr)^{\langle d\rangle},$$
--   the subtraction being truncated subtraction of natural numbers and the recursive call being in degree $d$.
--
--   Thus the definition implements the greedy construction of the $d$-th Macaulay (binomial) representation $a = \binom{k_d}{d} + \binom{k_{d-1}}{d-1} + \cdots$, in which the leading index is the largest $k$ with $\binom{k}{d} \le a$ and the remainder is expanded in the next lower degree, and simultaneously sums the shifted binomials $\binom{k_i+1}{i+1}$ obtained by raising each index and each degree by one. The search bound $a+d+1$ is large enough that no admissible leading index is missed, since $\binom{k}{d+1} > a$ once $k$ exceeds $a+d+1$. Sample values: $a^{\langle 1\rangle} = \binom{a+1}{2}$, $0^{\langle d\rangle}=0$, $1^{\langle d\rangle}=1$, and $4^{\langle 2\rangle}=5$, coming from $4 = \binom{3}{2}+\binom{1}{1}$. This is the function occurring in Macaulay's bound $h(d+1) \le h(d)^{\langle d\rangle}$ for Hilbert functions of homogeneous quotients of a polynomial ring and in the statements of Gotzmann's persistence and regularity theorems.
--
--   **Relation to Mathlib.** Mathlib has no Macaulay pseudo-power; this is the project's own definition, built from `Nat.choose` and `Nat.findGreatest`.
--
--   **Where it is used.** The function supplies the numerical vocabulary for Macaulay's growth bound on Hilbert functions and for Gotzmann's persistence theorem, which in turn underlie the construction of Hilbert schemes used as moduli-theoretic input in the project.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Nat_MacaulayPow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Nat

def macaulayPow : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d + 1, a =>
      (Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1) + 1).choose (d + 2) +
        macaulayPow d (a - (Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)).choose (d + 1))

end Nat



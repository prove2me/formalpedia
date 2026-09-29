-- Prove2me | Definitions.Def_Polynomial_DeuringPolynomial
-- name    : Polynomial_DeuringPolynomial
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/33384e93-1c13-5f02-823f-faf689f40c42
-- title:
--   The Deuring polynomial of a natural number
-- statement:
--   This module introduces a single object, [`Polynomial.deuringPolynomial`](../def/Polynomial_DeuringPolynomial.html#L9), which attaches to a natural number $q$ an element of $\mathbb{Z}[X]$. Writing $m = (q-1)/2$ for the truncated natural-number quotient of the truncated predecessor $q-1$ (so $m = (q-1)/2$ exactly when $q$ is odd, $m = 0$ for $q \in \{0,1,2\}$), the definition is the finite sum
--   $$H_q(X) \;=\; \sum_{i=0}^{m} \binom{m}{i}^{2} X^{i},$$
--   the $i$-th coefficient being the integer $\binom{m}{i}^2$, obtained as the square of the binomial coefficient $\binom{m}{i}$ viewed in $\mathbb{Z}$, and the index $i$ running over $\{0, 1, \dots, m\}$. Thus the polynomial is monic of degree $m$, has constant term $1$, is palindromic, and specialises at $X = 1$ to $\binom{2m}{m}$.
--
--   Two points about the shape of the definition are worth noting. First, the polynomial is indexed by $q$ rather than by $m$: the passage from $q$ to $m = (q-1)/2$ is built into the definition, so that statements about $H_q$ for an odd prime $q$ can be made directly in terms of $q$. Second, the definition uses natural-number subtraction and division, so it returns a well-defined integer polynomial for every natural number $q$, with no primality or parity hypothesis; for even $q$ the value is whatever the truncated arithmetic produces rather than anything of classical significance. No supersingularity property is part of the definition: `deuringPolynomial` is purely the above binomial-square generating polynomial, and the classical characterisation of its roots modulo $q$ is the content of separate theorems.
--
--   **Relation to Mathlib.** Mathlib has no Deuring (Hasse) polynomial for the Legendre family; this is the project's own definition, built from Mathlib's `Polynomial` and `Nat.choose`.
--
--   **Where it is used.** Modulo an odd prime $q$, $H_q$ is the classical Hasse polynomial of the Legendre family: the curve $y^2 = x(x-1)(x-\lambda)$ in characteristic $q$ is supersingular precisely when $H_q(\lambda) = 0$. The polynomial is therefore the basic tool for the characteristic-$q$ analysis of supersingular elliptic curves and for counting supersingular invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Polynomial_DeuringPolynomial.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

namespace Polynomial

noncomputable def deuringPolynomial (q : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range ((q - 1) / 2 + 1), C ((((q - 1) / 2).choose i : ℤ) ^ 2) * X ^ i

end Polynomial



-- Prove2me | Definitions.Def_ShorAlgorithms_Reduction_localOrder
-- name    : ShorAlgorithms_Reduction_localOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T08:23:16.354113+00:00
-- url     : https://prove2.me/theorems/6b803f04-7a1a-4b80-b288-8c9f5e4804fc
-- title:
--   The local orders r_p: the order of x modulo the prime power p^α exactly dividing n
-- statement:
--   Let $n = \prod_{i=1}^k p_i^{\alpha_i}$ be the prime factorization of $n \ge 1$ and let $x$ be a unit modulo $n$. For each prime factor $p = p_i$ with exponent $\alpha = \alpha_i$, reduction modulo $p^\alpha$ is a ring homomorphism $\mathbb{Z}/n \to \mathbb{Z}/p^\alpha$, and the image $x \bmod p^\alpha$ is a unit. The **local order**
--
--   $$
--   r_p = \operatorname{ord}_{p^{\alpha}}(x)
--   $$
--
--   is the multiplicative order of $x$ modulo $p^\alpha$ — the full prime power dividing $n$, not the prime $p$ itself. It is a positive integer since the unit group modulo $p^\alpha$ is finite.
--
--   These are the numbers $r_i$ of Shor's sketch, whose 2-adic valuations decide whether the reduction succeeds.
--
--   **Formalization Note** `localUnit n u p` is the image of `u` under `Units.map` of `ZMod.castHom` into `ZMod (p ^ n.factorization p)`; `localOrder n u p = orderOf (localUnit n u p)`. The definition is total in `p`: for a `p` that is not a prime factor of `n` the modulus is $p^0 = 1$ and the order is $1$; every theorem of the mission uses it only for `p ∈ n.primeFactors`.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1498, §5, "Suppose that n = ∏_{i=1}^k p_i^{α_i} is the prime factorization of n. Let r_i be the order of x (mod p_i^{α_i})."

import Mathlib

namespace ShorAlgorithms.Reduction

/-- Shor (1997), §5, p. 1498: for `n = ∏ p_i^{α_i}` and a unit `x (mod n)`, the reduction
`x (mod p^α)` of `x` modulo the full prime power `p^α = p ^ n.factorization p` dividing `n`,
as a unit of `ZMod (p^α)` (the image of a unit under the reduction ring homomorphism).
For `p` not a prime factor of `n` the modulus is `p^0 = 1` and the unit is trivial. -/
def localUnit (n : ℕ) (u : (ZMod n)ˣ) (p : ℕ) : (ZMod (p ^ n.factorization p))ˣ :=
  Units.map (ZMod.castHom (Nat.ordProj_dvd n p) (ZMod (p ^ n.factorization p))).toMonoidHom u

/-- Shor (1997), §5, p. 1498: `r_i`, "the order of `x (mod p_i^{α_i})`", i.e. the
multiplicative order of `x` modulo the prime power `p^α` exactly dividing `n`
(not modulo `p`). It is `≥ 1` because the unit group of `ZMod (p^α)` is finite. -/
noncomputable def localOrder (n : ℕ) (u : (ZMod n)ˣ) (p : ℕ) : ℕ :=
  orderOf (localUnit n u p)

end ShorAlgorithms.Reduction



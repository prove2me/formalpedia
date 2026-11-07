-- Prove2me | Definitions.Def_PRUPermLayer_collisionAccept
-- name    : PRUPermLayer_collisionAccept
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:32.012212+00:00
-- url     : https://prove2.me/theorems/b9eba3c6-1856-44ee-8d49-481bf5bce530
-- title:
--   Acceptance probability of the $t$-query collision test for a fixed oracle
-- statement:
--   The **$t$-query collision test** queries $|0^n\rangle$ $t$ times, measures every output in the computational basis, and accepts if two outcomes are equal. For a fixed oracle $U$ the $t$ outcomes are independent samples from $p_x = |\langle x|U|0^n\rangle|^2$, so the test accepts with probability
--   $$
--   1 - \sum_{\substack{x_1,\dots,x_t \\ \text{pairwise different}}} \ \prod_{i=1}^t p_{x_i} .
--   $$
--   It is the attack behind the lower half of Theorem 1.1(ii).
--
--   **Formalization Note** Sanity: with $U = I$ and $t = 2$ it accepts with probability $1$; with $t = 1$ it never accepts.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), proof of Theorem 1.1, part (ii), p.19 (PDF p.21)

import Mathlib
import Definitions.Def_PRUPermLayer_outDist

namespace PRUPermLayer

/-- The acceptance probability of the `t`-query collision test with a fixed oracle `U`
(Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), proof of Theorem 1.1, part (ii), lower bound, p.19 (PDF p.21): "The algorithm queries |0n⟩
t times, measures every output in the computational basis, and accepts if two outcomes are
equal. For a fixed oracle U the t outcomes are independent samples from the distribution
px = |⟨x|U|0n⟩|2"): the probability that `t` independent samples from `p` are not pairwise
different,
`1 − Σ_{x injective} ∏ᵢ p_{x_i}`.

**Formalization Note** Sanity: `collisionAccept n 2 1 = 1` and `collisionAccept n 1 U = 0` for
unitary `U`. -/
noncomputable def collisionAccept (n t : ℕ) (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : ℝ :=
  1 - ∑ x ∈ Finset.univ.filter (fun x : Fin t → Fin (2 ^ n) => Function.Injective x),
    ∏ i, outDist U (x i)

end PRUPermLayer



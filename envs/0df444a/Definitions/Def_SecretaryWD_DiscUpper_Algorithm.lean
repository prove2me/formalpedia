-- Prove2me | Definitions.Def_SecretaryWD_DiscUpper_Algorithm
-- name    : SecretaryWD_DiscUpper_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:59:24.536783+00:00
-- url     : https://prove2.me/theorems/4b627ef7-2543-4df8-8f3a-c407996b0396
-- title:
--   The algorithm $\mathcal A$ of Theorem 4.4: a random discount class, then the classical rule on it
-- statement:
--   The algorithm $\mathcal A$ of Theorem 4.4 knows the discount function $d$ (hence $n$, $d_{\max}$ and the classes $P_c$) but not the values. Let
--   $$M = 3\lceil \log_2 n\rceil + 2 .$$
--   $\mathcal A$ chooses $c\in\{1,\dots,M\}$ uniformly at random and then runs $\mathcal A_c$: the classical secretary rule on the arrivals at the times of $P_c$ only, in time order. With $m=|P_c|$, $\mathcal A_c$ ignores every arrival at a time outside $P_c$, observes the first $\lfloor m/e\rfloor$ arrivals of $P_c$, and then selects the first arrival of $P_c$ whose element ranks, in the tie-break order (larger value first, smaller index on equal values), above every earlier arrival of $P_c$. Selecting at time $i$ earns $d(i)\,v(\pi(i))$; selecting nothing earns $0$. If $P_c=\emptyset$, $\mathcal A_c$ selects nothing.
--
--   The expected payoffs are
--   $$\mathbb E[\mathcal A_c]=\mathbb E_\pi[\text{payoff of }\mathcal A_c],\qquad \mathbb E[\mathcal A]=\frac1M\sum_{c=1}^{M}\mathbb E[\mathcal A_c].$$
--
--   This is the algorithm whose competitive ratio Theorem 4.4 bounds by $O(\log n)$.
--
--   **Formalization Note.** The logarithm is base $2$ (the classes are powers of $2$) and $\lceil\log_2 n\rceil$ is `Nat.clog 2 n`, so $M=2$ at $n=1$. The $k$-th time of $P_c$ (0-based, increasing) is `(P_c).orderEmbOfFin rfl k`. The algorithm's own coin is the explicit average $\frac1M\sum_{c=1}^M$.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 7, proof of Theorem 4.4 ("Our algorithm A chooses a c ∈ [3 log n+2] uniformly at random ...")

import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_DiscountedModel

namespace SecretaryWD.DiscUpper

/-- The number of discount classes the algorithm draws from, `M = 3⌈log₂ n⌉ + 2`. -/
def classCount (n : ℕ) : ℕ := 3 * Nat.clog 2 n + 2

/-- The payoff of `A_c` on order `π`: run the classical secretary rule on the arrivals at the
times of `P_c` only, in time order (the `k`-th time of `P_c` is `(P_c).orderEmbOfFin rfl k`),
comparing them by the tie-break key of the arriving element; if it selects the arrival at time
`i`, earn `d(i) · v(π(i))`, otherwise `0`. -/
noncomputable def classPayoff {n : ℕ} (d v : Fin n → ℝ) (c : ℕ) (π : Equiv.Perm (Fin n)) : ℝ :=
  match classicalSecretary (discountClass d c).card
      (fun k => tieKey v (π ((discountClass d c).orderEmbOfFin rfl k))) with
  | none => 0
  | some k =>
      d ((discountClass d c).orderEmbOfFin rfl k) *
        v (π ((discountClass d c).orderEmbOfFin rfl k))

/-- `E_π[A_c]`, the expected payoff of `A_c`. -/
noncomputable def classValue {n : ℕ} (d v : Fin n → ℝ) (c : ℕ) : ℝ :=
  uniformAvg fun π => classPayoff d v c π

/-- `E[A]` for the algorithm of Theorem 4.4: `c` uniform on `{1, …, M}`, then `A_c`. -/
noncomputable def algorithmValue {n : ℕ} (d v : Fin n → ℝ) : ℝ :=
  (1 / (classCount n : ℝ)) * ∑ c ∈ Finset.Icc 1 (classCount n), classValue d v c

end SecretaryWD.DiscUpper



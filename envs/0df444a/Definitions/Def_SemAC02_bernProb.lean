-- Prove2me | Definitions.Def_SemAC02_bernProb
-- name    : SemAC02_bernProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:26:50.325697+00:00
-- url     : https://prove2.me/theorems/4e2996ed-66f3-4ae4-a3d7-781b04ee0959
-- title:
--   Probabilities under $\mathrm{Bern}(p)^m$ and Hamming weight
-- statement:
--   $\mathrm{Bern}(p)^m$ is the distribution of $m$ independent bits, each equal to $1$ with probability $p$. For an event $E\subseteq\{0,1\}^m$,
--   $$
--   \Pr_{x\sim\mathrm{Bern}(p)^m}[x\in E]=\sum_{x\in E}\prod_{i=1}^m p^{x_i}(1-p)^{1-x_i}.
--   $$
--   The **Hamming weight** $|x|$ is the number of ones of $x$.
--
--   **Formalization Note** The probability is the finite sum; it is a probability for $0\le p\le1$.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §8.3, p.66 (PDF p.68)

import Mathlib

namespace SemAC02

/-- `Pr_{x ∼ Bern(p)^m}[E(x)]` (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard
Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission), §8.3, p.66):
`Bern(p)^m` is the distribution of `m` independent bits, each equal to `1` with probability `p`.

**Formalization Note** The probability is the finite sum `∑_{x ∈ {0,1}^m, E(x)} ∏_i p^{x_i}
(1 − p)^{1 − x_i}`; it is a probability for `0 ≤ p ≤ 1`. -/
noncomputable def bernProb (p : ℝ) {m : ℕ} (E : (Fin m → Bool) → Bool) : ℝ :=
  ∑ x : Fin m → Bool, if E x then ∏ i, (if x i then p else 1 - p) else 0

/-- The Hamming weight `|x|`, the number of ones of `x ∈ {0,1}^m`. -/
def hammingWeight {m : ℕ} (x : Fin m → Bool) : ℕ := (Finset.univ.filter (fun i => x i = true)).card

end SemAC02



-- Prove2me | Definitions.Def_QPACLarge_IsMajorityBiasConst
-- name    : QPACLarge_IsMajorityBiasConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:07:40.85655+00:00
-- url     : https://prove2.me/theorems/2814b3cc-d205-499a-af6a-2b67a4b2548a
-- title:
--   A constant $b$ with the property of Lemma 3.5
-- statement:
--   A real $b$ is a **majority-bias constant** if $0 < b \le 1$ and, for every $n \ge 1$ with $N = 2^n$ and every odd $m$ with $1 \le m \le N$,
--   $$
--   \mathbb E[\mathrm{Sign}(B_1, \dots, B_m)] \ge b\sqrt{m/N}
--   $$
--   for independent signs $B_i$ of mean $1/\sqrt N$. Lemma 3.5 says such a constant exists; Theorem 3.6 is stated for "the constant in Lemma 3.5", i.e. for any such $b$.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 3.5, p.28; Section 2.1, p.14 ($N = 2^n$)

import Mathlib
import Definitions.Def_QPACLarge_majBias

namespace QPACLarge

/-- **A constant `b` as in Lemma 3.5.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 3.5, p.28: "a universal constant `0 < b ≤ 1` such that, for every odd integer `m` with
`1 ≤ m ≤ N`, independent signs `B₁, …, B_m ∈ {−1, +1}` of mean `1/√N` satisfy
`E[Sign(B₁, …, B_m)] ≥ b √(m/N)`", with `N = 2ⁿ`, `n ≥ 1` (Section 2.1, p.14).

**Formalization Note.** Lemma 3.5 is `∃ b, IsMajorityBiasConst b`; Theorem 3.6 refers to "the
constant in Lemma 3.5" through this property. -/
def IsMajorityBiasConst (b : ℝ) : Prop :=
  0 < b ∧ b ≤ 1 ∧ ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, Odd m → m ≤ 2 ^ n →
    b * Real.sqrt ((m : ℝ) / 2 ^ n) ≤ majBias (2 ^ n) m

end QPACLarge



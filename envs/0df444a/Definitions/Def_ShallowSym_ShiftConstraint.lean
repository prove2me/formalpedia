-- Prove2me | Definitions.Def_ShallowSym_ShiftConstraint
-- name    : ShallowSym_ShiftConstraint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:24.408789+00:00
-- url     : https://prove2.me/theorems/43737f27-0844-4ff7-8dd3-74b0339bdcbd
-- title:
--   The shift constraint $\sum_i s_i\equiv\binom k2-t \pmod k$, eqs. (2)/(4)
-- statement:
--   Shifts $s_1,\dots,s_k\in\{0,1,\dots,k-1\}$ for a test of weight $t$ modulo $k$ must satisfy
--
--   $$\sum_{i=1}^{k} s_i \equiv \binom{k}{2} - t \pmod k.$$
--
--   Under this constraint a passing test certifies $|x|\equiv t\pmod k$.
--
--   **Formalization Note** Shifts are `s : Fin k → ZMod k` (blocks indexed from $0$); $\binom k2$ and $t$ are cast into `ZMod k`.
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §3 eq. (2), p.8; §4 eq. (4), p.11

import Mathlib

namespace ShallowSym

/-- Constraint (2)/(4) on the shifts of a test for weight `t` modulo `k`:
`∑_{i=1}^k s_i ≡ (k choose 2) − t (mod k)`.

V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…), §3 eq. (2), p.8 and §4 eq. (4), p.11: "fixes shifts s1, …, sk ∈ {0, 1, …, k − 1}
satisfying ∑_{i=1}^{k} si ≡ (k choose 2) − t (mod k)."

**Formalization Note.** Shifts are `s : Fin k → ZMod k` (0-based block index); `k choose 2`
and `t` are cast into `ZMod k`. -/
def ShiftConstraint (k t : ℕ) (s : Fin k → ZMod k) : Prop :=
  ∑ i, s i = ((k.choose 2 : ℕ) : ZMod k) - ((t : ℕ) : ZMod k)

end ShallowSym



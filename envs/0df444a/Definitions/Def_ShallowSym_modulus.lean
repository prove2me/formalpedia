-- Prove2me | Definitions.Def_ShallowSym_modulus
-- name    : ShallowSym_modulus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:32.774798+00:00
-- url     : https://prove2.me/theorems/df8775a5-a4b9-4fc8-8068-6553bb885608
-- title:
--   The moduli $k_i$: the smallest power of the $i$-th prime greater than $n^{1/(d-1)}$
-- statement:
--   For depth $d\ge 2$ and $n$ variables, the $i$-th modulus of the construction is the smallest power of the $i$-th prime $p_i$ that is greater than $n^{1/(d-1)}$:
--
--   $$k_i = p_i^{\,a_i},\qquad a_i=\min\{\, a\in\mathbb N : n^{1/(d-1)} < p_i^{\,a}\,\}.$$
--
--   The tests for $|x|=t$ combine one test for each modulus $k_1,\dots,k_{d-1}$.
--
--   **Formalization Note** The primes are indexed from $0$: $p_i$ is `Nat.nth Nat.Prime i`, so $p_0=2$ is the paper's $p_1$. $n^{1/(d-1)}$ is the real power `(n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) - 1))`. The minimum is `sInf` of a set of natural numbers that is nonempty for all $n,d,i$ (since $p_i\ge 2$), so it is a true minimum.
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §4 'Anatomy of a test', p.11

import Mathlib

namespace ShallowSym

/-- The `i`-th modulus of the depth-`d` construction on `n` variables: the smallest power of
the `i`-th prime `p_i` that is greater than `n^{1/(d−1)}`,
`k_i = p_i ^ min {a ∈ ℕ | n^{1/(d−1)} < p_i^a}`.

V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…), §4 p.11: "We can arrange this by making ki the smallest power of the ith prime pi that is
greater than n^{1/(d−1)}".

**Formalization Note.**
* The prime index is 0-based: `p_i = Nat.nth Nat.Prime i`, so `p_0 = 2` is the paper's `p_1`.
* `n^{1/(d−1)}` is the real power `(n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) - 1))`.
* The exponent is `sInf` of a set of naturals; the set is nonempty for every `n, d, i` because
  `p_i ≥ 2`, so `sInf` is its minimum (it never takes the empty-set value). -/
noncomputable def modulus (d n i : ℕ) : ℕ :=
  Nat.nth Nat.Prime i ^
    sInf {a : ℕ | (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) - 1)) < ((Nat.nth Nat.Prime i : ℕ) : ℝ) ^ a}

end ShallowSym



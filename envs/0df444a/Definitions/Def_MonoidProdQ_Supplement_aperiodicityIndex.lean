-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_aperiodicityIndex
-- name    : MonoidProdQ_Supplement_aperiodicityIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:06:36.122879+00:00
-- url     : https://prove2.me/theorems/93359b4b-75f8-4e6e-9611-cb26f7e02c1d
-- title:
--   Aperiodicity index $\iota(M)$
-- statement:
--   For a finite aperiodic monoid $M$, the **aperiodicity index** $\iota(M)$ is the least integer $k\ge1$ such that
--
--   $$a^k=a^{k+1}\qquad\text{for every }a\in M.$$
--
--   It is the smallest uniform exponent at which every element's powers stabilize, and it controls the lower bound of Theorem 13.
--
--   **Formalization Note** Defined as the natural-number infimum of $\{k\ge1:\forall a,\ a^k=a^{k+1}\}$. For a finite aperiodic monoid this set is nonempty, so the infimum is attained and is at least $1$; on an empty set (infinite or nonaperiodic $M$) it would be the junk value $0$, and every statement using $\iota(M)$ assumes $M$ finite and aperiodic.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, p.26

import Mathlib

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, p.26: "the aperiodicity index ι(M) of a
finite aperiodic monoid M is the least integer k ≥ 1 such that a^k = a^{k+1} for every a ∈ M."

**Formalization Note.** The least element of `{k ≥ 1 : ∀ a, aᵏ = aᵏ⁺¹}` as a natural-number
infimum. For a finite aperiodic monoid the set is nonempty (take the maximum of the individual
exponents: `aᵏ = aᵏ⁺¹` propagates to all larger exponents), so the infimum is attained and is at
least `1`. On an empty set (an infinite or nonaperiodic monoid) `sInf` returns the junk value
`0`; every statement using `ι(M)` assumes `M` finite and aperiodic. -/
noncomputable def aperiodicityIndex (M : Type*) [Monoid M] : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ ∀ a : M, a ^ k = a ^ (k + 1)}

end MonoidProdQ.Supplement



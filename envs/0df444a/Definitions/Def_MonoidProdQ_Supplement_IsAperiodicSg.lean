-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_IsAperiodicSg
-- name    : MonoidProdQ_Supplement_IsAperiodicSg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:06:23.355579+00:00
-- url     : https://prove2.me/theorems/93c1bae3-69d0-42f6-8201-f84895c38e55
-- title:
--   Aperiodic semigroup
-- statement:
--   A semigroup $S$ (an associative operation, no identity required) is **aperiodic** if for every $a\in S$ there is an integer $k\ge 1$ with
--
--   $$a^k=a^{k+1}.$$
--
--   A finite semigroup is **nonaperiodic** when this fails for some element; equivalently it contains a nontrivial subgroup. Theorems 12 and 77 use this notion for semigroups; for monoids it coincides with the published aperiodicity predicate of the base mission.
--
--   **Formalization Note** A semigroup has no power operation; the positive power $a^k$ ($k\ge1$) is the published semigroup power `FanInSemigroup.ppow` (the product of $k$ copies of $a$, exponent a positive natural number). This is the paper's power-based definition; the published `FanInSemigroup.IsGroupfree` (no nontrivial subgroup) is an equivalent property of finite semigroups but a different definition, so it is not reused.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §1, p.4; Theorems 12, 77, pp.25, 92

import Definitions.Def_FanInSemigroup_wordProd

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §1, p.4 (aperiodicity, "for every element
a there is a k ≥ 1 such that a^k = a^{k+1}"), applied to a semigroup as in Theorems 12 and 77
(pp.25, 92): a semigroup `S` is aperiodic if every `a ∈ S` has `a^k = a^{k+1}` for some `k ≥ 1`.

**Formalization Note.** A semigroup carries no power operation; the positive power `a^k`,
`k ≥ 1`, is the published `FanInSemigroup.ppow a k` (the product of `k` copies of `a`, with the
exponent in `ℕ+`). For a monoid this is the published `MonoidProdQ.IsAperiodic`.
"Nonaperiodic" is the negation. -/
def IsAperiodicSg (S : Type*) [Semigroup S] : Prop :=
  ∀ a : S, ∃ k : ℕ+, FanInSemigroup.ppow a k = FanInSemigroup.ppow a (k + 1)

end MonoidProdQ.Supplement



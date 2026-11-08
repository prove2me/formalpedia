-- Prove2me | Definitions.Def_SingleInteraction_SIHInstance_Valid
-- name    : SingleInteraction_SIHInstance_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:54:28.718214+00:00
-- url     : https://prove2.me/theorems/51d9a7d8-12c8-4121-bf51-486cf0b2238a
-- title:
--   Valid inputs of $\mathrm{SIH}_k$
-- statement:
--   An input $(n,L,a,b)$ is valid for $k$ and the polynomial exponent $c$ when
--
--   1. every tuple has exactly $k$ entries, all in $\{0,\dots,n-1\}$ and pairwise distinct;
--   2. the tuples are pairwise distinct as ordered tuples (so $(u,v)$ and $(v,u)$ may both occur, but no ordered tuple twice);
--   3. the thresholds are valid (`ThresholdsValid`).
--
--   **Formalization Note** The number $M$ of tuples needs no separate bound: distinct ordered tuples of distinct qubits number at most $n^k$. There are no weights.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 31, pp.29–30

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_SIHInstance
import Definitions.Def_SingleInteraction_ThresholdsValid

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- Validity of a single-interaction `k`-local input for the polynomial exponent `c` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…),
Definition 31, pp.29–30): "a set `L` of `M = poly(n)` pairwise distinct ordered `k`-tuples
`e = (v1, . . . , vk)` of physical qubits, where `v1, . . . , vk` are pairwise distinct within each tuple,
and two real numbers `a, b` specified with `poly(n)` bits of precision such that `b − a ≥ 1/poly(n)`".

1. every tuple has length `k`, entries in `{0, …, n−1}`, and pairwise distinct entries;
2. the tuples are pairwise distinct as ordered tuples (both `(u, v)` and `(v, u)` may occur);
3. the thresholds satisfy `ThresholdsValid n c a b`.

**Formalization Note** No separate clause bounds `M`: pairwise distinct ordered tuples of distinct qubits
number at most `n^k`, a polynomial for constant `k`. Every tuple carries weight one: the instance has no
coefficients. -/
def SIHInstance.Valid (k c : ℕ) (x : SIHInstance) : Prop :=
  (∀ l ∈ x.tuples, l.length = k ∧ (∀ v ∈ l, v < x.n) ∧ l.Nodup) ∧ x.tuples.Nodup ∧
    ThresholdsValid x.n c x.a x.b

end SingleInteraction



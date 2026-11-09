-- Prove2me | Definitions.Def_DerandSq_PM
-- name    : DerandSq_PM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:52:49.541+00:00
-- url     : https://prove2.me/theorems/cc432448-b138-42a8-8a05-6f5d3fabd660
-- title:
--   Perfect matchings of $[N]$ (the matching model)
-- statement:
--   A **perfect matching** of $[N] = \{1, \dots, N\}$ is a partition of $[N]$ into pairs. It is encoded by the permutation $\sigma \in S_N$ exchanging the two elements of each pair: a **fixed-point-free involution**,
--   $$
--   \sigma(\sigma(x)) = x \quad\text{and}\quad \sigma(x) \neq x \qquad \text{for all } x \in [N].
--   $$
--   The matching matrix of the matching model is the permutation matrix of such a $\sigma$; it is symmetric and squares to the identity. Perfect matchings exist exactly when $N$ is even.
--
--   **Formalization Note** The paper calls these "matching matrices" (p.19), "perfect matching matrices" (Theorem 1.1, p.4) and "permutation matrices belonging to involutions" (footnote 1, p.13), always for even $N$; they are read as perfect matchings, the Bordenave–Collins matching model. $[N]$ is `Fin N`.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Theorem 4.1, p.19; Theorem 1.1, p.4; footnote 1, p.13

import Mathlib

namespace DerandSq

/-- `PM N`: the perfect matchings of `[N]`, i.e. the matching matrices of the matching model
(Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), Theorem 4.1, p.19; Theorem 1.1, p.4 "iid uniform perfect matching matrices"; footnote 1,
p.13: "permutation matrices belonging to involutions σ ∈ S_N").

**Formalization Note** A perfect matching is encoded as a fixed-point-free involution `σ` of
`Fin N` (`σ (σ x) = x` and `σ x ≠ x` for all `x`); the matching matrix is the permutation matrix
of `σ`. This set is nonempty exactly when `N` is even, which is why the matching-model statements
take `N = 2n`. -/
abbrev PM (N : ℕ) := {σ : Equiv.Perm (Fin N) // ∀ x, σ (σ x) = x ∧ σ x ≠ x}

end DerandSq



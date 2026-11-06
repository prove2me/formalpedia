-- Prove2me | Definitions.Def_GeomDRSub_Before
-- name    : GeomDRSub_Before
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:12:09.731974+00:00
-- url     : https://prove2.me/theorems/7a04d1c0-876a-4656-b1ba-04f2f92b1c35
-- title:
--   The processing order $\pi$ (ties by coordinate index)
-- statement:
--   Let $\pi$ be the permutation of $[d]$ with $\mu_{\pi(1)}\le\cdots\le\mu_{\pi(d)}$, ties resolved by increasing original coordinate index. Coordinate $j$ is **processed before** coordinate $i$ when
--   $$
--   \mu_j<\mu_i\quad\text{or}\quad(\mu_j=\mu_i\ \text{and}\ j<i),
--   $$
--   that is, when $\pi^{-1}(j)<\pi^{-1}(i)$.
--
--   **Formalization Note** The permutation is represented by this strict total order on the coordinates instead of a sorting function.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 4.1, p.10, after Eq. (12)

import Mathlib
import Definitions.Def_GeomDRSub_muW

namespace GeomDRSub

/-- **The processing order `π`.** Aggarwal–Lu, arXiv:2610.00545, Section 4.1, p.10: "Let
`π : [d] → [d]` be the permutation of the coordinates such that `µ_{π(1)} ≤ ⋯ ≤ µ_{π(d)}`, with ties
resolved by increasing original coordinate index."

`Before ζ x j i` says that coordinate `j` is processed strictly before coordinate `i`, i.e.
`π⁻¹(j) < π⁻¹(i)`: either `µⱼ < µᵢ`, or `µⱼ = µᵢ` and `j < i`.

**Formalization Note.** The permutation is encoded by this strict total order on `Fin d` instead of
a sorting function; the two determine each other. -/
def Before {d : ℕ} (ζ : ℝ) (x : EuclideanSpace ℝ (Fin d)) (j i : Fin d) : Prop :=
  muW ζ x j < muW ζ x i ∨ (muW ζ x j = muW ζ x i ∧ j < i)

end GeomDRSub



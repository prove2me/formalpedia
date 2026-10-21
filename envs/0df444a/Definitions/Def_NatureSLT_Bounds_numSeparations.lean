-- Prove2me | Definitions.Def_NatureSLT_Bounds_numSeparations
-- name    : NatureSLT_Bounds_numSeparations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:45.181284+00:00
-- url     : https://prove2.me/theorems/dc0cfd38-99f8-493c-a61c-89ba8a919c74
-- title:
--   Number of separations $N^\Lambda(z_1, \dots, z_\ell)$ of a sample by a set of indicator functions
-- statement:
--   Let $Q(z, \alpha)$, $\alpha \in \Lambda$, be a set of indicator functions on a set $Z$ (functions taking only the values $0$ and $1$), indexed by an arbitrary parameter set $\Lambda$, and let $z_1, \dots, z_\ell \in Z$ be a sample of size $\ell$. Each parameter $\alpha$ produces the binary vector
--   $$q(\alpha) = \big(Q(z_1, \alpha), \dots, Q(z_\ell, \alpha)\big) \in \{0, 1\}^\ell .$$
--   The quantity $N^\Lambda(z_1, \dots, z_\ell)$ is the number of **different** vectors $q(\alpha)$ obtained as $\alpha$ ranges over $\Lambda$, i.e. the number of different separations of the sample $z_1, \dots, z_\ell$ by functions of the set; geometrically, the number of vertices of the $\ell$-dimensional cube reached by the set on the sample. It satisfies $N^\Lambda(z_1, \dots, z_\ell) \le 2^\ell$.
--
--   This counting function is the basic combinatorial object of the theory of bounds: the VC entropy, the annealed entropy and the growth function are all built from it.
--
--   **Formalization Note** The sample is a function $z : \{0, \dots, \ell - 1\} \to Z$ and the functions are real valued, $Q : \Lambda \to Z \to \mathbb R$; the count is the cardinality (`Set.ncard`) of the range of $\alpha \mapsto q(\alpha)$. The count is meaningful for $\{0,1\}$-valued $Q$, where the range is finite; every theorem of this mission that applies it assumes this (or applies it to the level indicators, which are $\{0,1\}$-valued by construction). For an infinite range `Set.ncard` would return $0$, which never occurs under those hypotheses.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 42, Section 2.3.2; p. 55, Section 2.7

import Mathlib

namespace NatureSLT.Bounds

/-- Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., p. 42, §2.3.2 (and p. 55, §2.7):
for a set of indicator functions `Q(z, α)`, `α ∈ Λ`, and a sample `z₁, …, z_ℓ`, the quantity
`N^Λ(z₁, …, z_ℓ)` is the number of different binary vectors
`q(α) = (Q(z₁, α), …, Q(z_ℓ, α))`, `α ∈ Λ`, i.e. the number of different separations of the
sample by the set. For a `{0, 1}`-valued `Q` the set of vectors is finite (at most `2^ℓ`). -/
noncomputable def numSeparations {Λ Z : Type*} (Q : Λ → Z → ℝ) {ℓ : ℕ} (z : Fin ℓ → Z) : ℕ :=
  Set.ncard (Set.range fun α : Λ => fun i : Fin ℓ => Q α (z i))

end NatureSLT.Bounds



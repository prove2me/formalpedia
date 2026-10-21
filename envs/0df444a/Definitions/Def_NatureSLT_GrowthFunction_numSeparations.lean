-- Prove2me | Definitions.Def_NatureSLT_GrowthFunction_numSeparations
-- name    : NatureSLT_GrowthFunction_numSeparations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:03.923299+00:00
-- url     : https://prove2.me/theorems/4ea97dfe-fa6f-4ec1-84be-345c6d303034
-- title:
--   Number of separations $N^\Lambda(z_1, \dots, z_\ell)$ of a sample by indicator functions
-- statement:
--   Let $Q(z, \alpha)$, $\alpha \in \Lambda$, be a set of indicator functions on a set $Z$, i.e. functions taking only the two values $0$ and $1$, and let $z_1, \dots, z_\ell$ be a sample of points of $Z$ (repetitions allowed). Each parameter $\alpha$ produces the $\ell$-dimensional binary vector
--
--   $$q(\alpha) = \bigl(Q(z_1, \alpha), \dots, Q(z_\ell, \alpha)\bigr), \qquad \alpha \in \Lambda .$$
--
--   The quantity $N^\Lambda(z_1, \dots, z_\ell)$ is the number of different vectors $q(\alpha)$ obtained as $\alpha$ ranges over $\Lambda$: geometrically, the number of different vertices of the $\ell$-dimensional cube that the set of functions realizes on the sample, i.e. the number of different separations of the sample. It is a natural number between $1$ and $2^\ell$ when $\Lambda$ is nonempty.
--
--   This is the combinatorial quantity on which the entropy, the annealed entropy and the growth function of the set of indicator functions are built.
--
--   **Formalization Note** Indicator values are encoded as booleans, `true` standing for $1$ and `false` for $0$; the function is written `Q α z` for the book's $Q(z, \alpha)$. The sample is a map from `Fin ℓ` (indices $0, \dots, \ell - 1$) to $Z$. The count is the cardinality of the (finite) set of realized vectors; it is $0$ when $\Lambda$ is empty.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 42, Section 2.3.2

import Mathlib

namespace NatureSLT.GrowthFunction

/-- **N^Λ(z₁, …, z_ℓ)** (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §2.3.2,
p. 42). For a set of indicator functions `Q(z, α)`, `α ∈ Λ`, and a sample `z₁, …, z_ℓ`, the
number of different binary vectors `q(α) = (Q(z₁, α), …, Q(z_ℓ, α))`, `α ∈ Λ`: the number of
different vertices of the `ℓ`-dimensional cube obtained on the sample.

Indicator functions take the two values `0` and `1`; here they are `Bool`-valued, `true` standing
for the value `1` and `false` for `0`. The parameter `α` comes first: `Q α z` is the book's
`Q(z, α)`. The sample is indexed by `Fin ℓ` (the book's `z₁, …, z_ℓ` is `z 0, …, z (ℓ - 1)`) and
may repeat points. The set of vectors lies in the finite type `Fin ℓ → Bool`, so it is finite
and `ncard` is its number of elements (at most `2^ℓ`; `0` exactly when `Λ` is empty). -/
noncomputable def numSeparations {Z Λ : Type*} (Q : Λ → Z → Bool) {ℓ : ℕ} (z : Fin ℓ → Z) : ℕ :=
  (Set.range fun α : Λ => fun i : Fin ℓ => Q α (z i)).ncard

end NatureSLT.GrowthFunction



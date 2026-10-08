-- Prove2me | Definitions.Def_HScattered_LinearSets_LinearSet
-- name    : HScattered_LinearSets_LinearSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:11.076986+00:00
-- url     : https://prove2.me/theorems/5ba79f0b-9093-464d-9261-b7c9fda98a0b
-- title:
--   The 𝔽_q-linear set L_U of PG(V, 𝔽_{qⁿ})
-- statement:
--   Let $\mathbb F_q \subseteq \mathbb F_{q^n}$ be fields and let $V$ be a vector space over $\mathbb F_{q^n}$, so that $\Lambda = \mathrm{PG}(V,\mathbb F_{q^n})$ is the projective space whose points are the one-dimensional $\mathbb F_{q^n}$-subspaces of $V$. For an $\mathbb F_q$-subspace $U$ of $V$, the **$\mathbb F_q$-linear set** defined by $U$ is the set of points spanned by the nonzero vectors of $U$:
--
--   $$
--   L_U = \{\langle u\rangle_{\mathbb F_{q^n}} : u \in U\setminus\{0\}\}.
--   $$
--
--   If $\dim_{\mathbb F_q} U = k$, the linear set is said to have rank $k$; different subspaces, even of different dimensions, can define the same point set. Linear sets are the objects whose equivalence Theorem 4.5 studies.
--
--   **Formalization Note** A point $\langle u\rangle_{\mathbb F_{q^n}}$ is represented by the `K`-submodule `K ∙ u` itself, so `linearSet F K U : Set (Submodule K V)`. The size $|L_U|$ is `Set.ncard` of this set.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 12, §4 (definition of L_U)

import Mathlib

namespace HScattered.LinearSets

/-- §4, p. 12 (arXiv:1906.10590v2). The `𝔽_q`-linear set defined by an `𝔽_q`-subspace `U`
of the `𝔽_{qⁿ}`-space `V`: the set of points `⟨u⟩_{𝔽_{qⁿ}}` of `PG(V, 𝔽_{qⁿ})`, `u ∈ U \ {0}`,
`L_U := {⟨u⟩_{𝔽_{qⁿ}} : u ∈ U \ {0}}`.
A point of `PG(V, K)` is represented by the one-dimensional `K`-subspace `K ∙ u` it is. -/
def linearSet (F K : Type*) {V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    (U : Submodule F V) : Set (Submodule K V) :=
  {P | ∃ u ∈ U, u ≠ 0 ∧ P = K ∙ u}

end HScattered.LinearSets



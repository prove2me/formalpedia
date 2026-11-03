-- Prove2me | Definitions.Def_WildeQIT_EntBreaking_cqChannel
-- name    : WildeQIT_EntBreaking_cqChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:11.707597+00:00
-- url     : https://prove2.me/theorems/7acc5987-a74c-4f98-891f-620dde3c7b23
-- title:
--   Classical–quantum (preparation) channel $\rho\mapsto\sum_k\langle k|\rho|k\rangle\sigma^k$ (Definition 4.6.6)
-- statement:
--   Let $\{\sigma^k_B\}_k$ be a family of operators on $\mathcal H_B$ indexed by a finite set, and let $\{|k\rangle\}$ be the standard orthonormal basis of the input system. The **classical–quantum channel** of the family is the linear map
--
--   $$
--   \mathcal P(X)=\sum_k \langle k|X|k\rangle\,\sigma^k_B ,
--   $$
--
--   which measures in the basis $\{|k\rangle\}$ and prepares $\sigma^k_B$ on outcome $k$. When every $\sigma^k_B$ is a density operator this is the channel (4.283) of Definition 4.6.6; that condition is a hypothesis of the statements that use it.
--
--   **Formalization Note** The measured basis is the standard basis of the input index type, so $\langle k|X|k\rangle$ is the diagonal entry $X_{kk}$. The book defines the map on density operators; its linear extension is the same formula.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 4.6.6, eq. (4.283), pp. 164–165

import Mathlib

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §4.6.5,
Definition 4.6.6 (Classical–Quantum Channel), (4.283), pp. 164–165.
-/

namespace WildeQIT.EntBreaking

open scoped Matrix

/-- **Definition 4.6.6 (Classical–Quantum Channel)**, Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, pp. 164–165: given an orthonormal basis `{|k⟩}` of the input and states
`σ^k_B ∈ D(ℋ_B)`, the classical–quantum channel measures in the basis `{|k⟩}` and prepares `σ^k_B`
on outcome `k`: `ρ ↦ ∑_k ⟨k|ρ|k⟩ σ^k_B` (4.283).

`cqChannel σ` is this map, extended linearly to all operators: `X ↦ ∑_k X_{kk} σ_k`. That every
`σ k` is a density operator is a hypothesis of the statements that use it.

**Formalization Note.** The input index type `k` is finite and `{|k⟩}` is its standard basis, so
`⟨k|X|k⟩ = X k k`. The linear extension of (4.283) from density operators to all operators is the
same formula (the book identifies a channel with its linear extension, p. 149). -/
def cqChannel {k b : Type} [Fintype k] (σ : k → Matrix b b ℂ) :
    Matrix k k ℂ →ₗ[ℂ] Matrix b b ℂ where
  toFun X := ∑ j, X j j • σ j
  map_add' X Y := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp [Finset.smul_sum, smul_smul]

end WildeQIT.EntBreaking



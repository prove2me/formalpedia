-- Prove2me | Definitions.Def_WildeQIT_EntBreaking_IsAdjointMap
-- name    : WildeQIT_EntBreaking_IsAdjointMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:13.202478+00:00
-- url     : https://prove2.me/theorems/1882ceaf-a755-4e02-887f-3e66f6b9b874
-- title:
--   Adjoint map $\langle Y,\mathcal N(X)\rangle=\langle\mathcal N^\dagger(Y),X\rangle$ (Definition 4.4.6)
-- statement:
--   Let $\mathcal N:\mathcal L(\mathcal H_A)\to\mathcal L(\mathcal H_B)$ be a linear map. With the Hilbert–Schmidt inner product $\langle C,D\rangle=\operatorname{Tr}\{C^\dagger D\}$ (Definition 4.4.5), the **adjoint** $\mathcal N^\dagger:\mathcal L(\mathcal H_B)\to\mathcal L(\mathcal H_A)$ is the unique linear map satisfying
--
--   $$
--   \langle Y,\mathcal N(X)\rangle=\langle \mathcal N^\dagger(Y),X\rangle\qquad\text{for all }X\in\mathcal L(\mathcal H_A),\ Y\in\mathcal L(\mathcal H_B).
--   $$
--
--   The predicate says that a given linear map $\mathcal N^\dagger$ satisfies these equations. The adjoint of a channel is its Heisenberg-picture description, used in Proposition 4.4.1.
--
--   **Formalization Note** The predicate records the defining equations (4.235). A linear map satisfying them exists and is unique in finite dimension, so a statement about every map satisfying the predicate is a statement about the adjoint.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definitions 4.4.5 and 4.4.6, eqs. (4.234)–(4.235), p. 157

import Mathlib

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §4.4.5,
Definition 4.4.5 (Hilbert–Schmidt Inner Product) and Definition 4.4.6 (Adjoint Map), p. 157.
-/

namespace WildeQIT.EntBreaking

open scoped Matrix

/-- **Definition 4.4.6 (Adjoint Map)**, Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 157. For a linear map `N : L(ℋ_A) → L(ℋ_B)`, the adjoint
`N† : L(ℋ_B) → L(ℋ_A)` is the unique linear map with `⟨Y, N(X)⟩ = ⟨N†(Y), X⟩` for all
`X ∈ L(ℋ_A)`, `Y ∈ L(ℋ_B)` (4.235), where `⟨C, D⟩ = Tr{C† D}` is the Hilbert–Schmidt inner
product (Definition 4.4.5, (4.234)). `IsAdjointMap N Nadj` says that the linear map `Nadj`
satisfies (4.235).

**Formalization Note.** The predicate records the defining equations (4.235); since a linear map
satisfying them is unique, a statement about every `Nadj` with `IsAdjointMap N Nadj` is a
statement about the adjoint `N†`. Such a map exists for every `N` (finite dimension). -/
def IsAdjointMap {a b : Type} [Fintype a] [Fintype b]
    (N : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ) (Nadj : Matrix b b ℂ →ₗ[ℂ] Matrix a a ℂ) : Prop :=
  ∀ (X : Matrix a a ℂ) (Y : Matrix b b ℂ), (Yᴴ * N X).trace = ((Nadj Y)ᴴ * X).trace

end WildeQIT.EntBreaking



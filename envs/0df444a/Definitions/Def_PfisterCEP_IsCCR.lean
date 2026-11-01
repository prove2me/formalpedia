-- Prove2me | Definitions.Def_PfisterCEP_IsCCR
-- name    : PfisterCEP_IsCCR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:05.430286+00:00
-- url     : https://prove2.me/theorems/2c6e216d-3770-414c-a9bb-16976c744fd0
-- title:
--   Canonical commutation relations of $N$ bosonic modes
-- statement:
--   Let $A$ be a complex algebra and $N\ge 0$. Two families $a_1,\dots,a_N$ and $a_1^\dagger,\dots,a_N^\dagger$ of elements of $A$ satisfy the **canonical commutation relations** (CCR) when, for all modes $k,l$,
--
--   $$[a_k,a_l^\dagger]=\delta_{kl}\,1,\qquad [a_k,a_l]=0,\qquad [a_k^\dagger,a_l^\dagger]=0,$$
--
--   where $[x,y]=xy-yx$. These are the relations of the annihilation and creation operators of the $N$ field modes $\{a_n\}_{1\dots N}$ of the paper.
--
--   **Formalization Note** The modes are indexed by `Fin N`; $a_k^\dagger$ is a separate family `ad`, not `star (a k)`. Only the algebraic relations are imposed; no topology is involved.
-- source:
--   Pfister, Graph states and carrier-envelope phase squeezing, arXiv:quant-ph/0701104v2, Sec. b, pp.1–2 (the modes of eqs. (1), (3), (4))

import Mathlib

namespace PfisterCEP

/-- **Canonical commutation relations of `N` bosonic modes.**
O. Pfister, *Graph states and carrier-envelope phase squeezing*, arXiv:quant-ph/0701104v2, Sec. b, pp.1–2 (the modes `{aₙ}₁…N` of the Hamiltonians (1), (3), (4); the dagger `a†ₙ`).

`IsCCR a ad` says that the families `a, ad : Fin N → A` in a complex algebra `A` satisfy
`[aₖ, a†ₗ] = δₖₗ`, `[aₖ, aₗ] = 0` and `[a†ₖ, a†ₗ] = 0`, with `ad k` playing the creation
operator `a†ₖ`.

**Formalization Note** `a†` is a separate family `ad` rather than `star ∘ a`: the statements of the
mission use only the commutation relations, and the adjoint family of a representation on a
Hilbert space is one instance. No topology is involved here. -/
def IsCCR {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ} (a ad : Fin N → A) : Prop :=
  (∀ k l, a k * ad l - ad l * a k = if k = l then (1 : A) else 0) ∧
    (∀ k l, a k * a l = a l * a k) ∧ (∀ k l, ad k * ad l = ad l * ad k)

end PfisterCEP



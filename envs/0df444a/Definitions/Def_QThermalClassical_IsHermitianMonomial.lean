-- Prove2me | Definitions.Def_QThermalClassical_IsHermitianMonomial
-- name    : QThermalClassical_IsHermitianMonomial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:20.013247+00:00
-- url     : https://prove2.me/theorems/7a98be2a-dd82-4e8d-900a-43b842d24532
-- title:
--   Hermitian monomials (Definition 3.1)
-- statement:
--   A **Hermitian monomial** $X$, with its term list $C(X)$, is built recursively (Definition 3.1): start from $X=I$, $C(I)=()$, and at each step replace
--   $$
--   \hat X=\tfrac12\left(E_1XE_2^\dagger+E_2XE_1^\dagger\right),\qquad C(\hat X)=C(X)\sqcup C(E_1)\sqcup C(E_2),
--   $$
--   where $E_1,E_2$ are Pauli products up to a phase (either may be the identity) and $\sqcup$ is concatenation (eqs. (76), (79)). The order of $X$ is $|C(X)|$ (eq. (77)) and its support is the union of the supports of the words of $C(X)$ (eq. (78)), not the support of the multiplied-out operator.
--
--   **Formalization Note** The identity is the Pauli product with empty term list, so no separate case is needed. The recursion admits any Pauli products up to a phase, which covers the outputs of the sampling primitive and their adjoints used in Algorithm 1.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 3.1, eqs. (76)–(79), pp.24–25

import Mathlib
import Definitions.Def_QThermalClassical_IsPauliProd

set_option autoImplicit false

namespace QThermalClassical

/-- Hermitian monomials (Definition 3.1), together with their term lists `C(X)`. Starting from
`X = I` with `C(I) = []`, one step of the recursion (76) replaces `X` by
`X̂ = ½ (E₁ X E₂^† + E₂ X E₁^†)` for Pauli products (up to a phase) `E₁, E₂`, either of which
may be the identity, and the term list by the concatenation (79)
`C(X̂) = C(X) ⊔ C(E₁) ⊔ C(E₂)`. The order (77) is the length of the term list, and the support
(78) is the union of the supports of its words (`wordsSupport`).

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 3.1, eqs. (76)–(79), pp.24–25.

**Formalization Note.** The identity is the Pauli product with empty term list and phase `1`,
so "either of which may be identity" needs no separate case. The recursion is stated for any
Pauli products, not only those returned by a sampler. -/
inductive IsHermitianMonomial {Q : Type} [Fintype Q] [DecidableEq Q] :
    Op Q → List (PauliWord Q) → Prop
  | base : IsHermitianMonomial 1 []
  | step {X E₁ E₂ : Op Q} {C C₁ C₂ : List (PauliWord Q)} :
      IsHermitianMonomial X C → IsPauliProd C₁ E₁ → IsPauliProd C₂ E₂ →
      IsHermitianMonomial ((1 / 2 : ℂ) • (E₁ * X * E₂.conjTranspose + E₂ * X * E₁.conjTranspose))
        (C ++ C₁ ++ C₂)

end QThermalClassical



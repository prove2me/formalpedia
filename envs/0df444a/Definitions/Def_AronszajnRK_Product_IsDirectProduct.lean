-- Prove2me | Definitions.Def_AronszajnRK_Product_IsDirectProduct
-- name    : AronszajnRK_Product_IsDirectProduct
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:34:08.762709+00:00
-- url     : https://prove2.me/theorems/1ee24426-e9db-4ae6-9c65-e95e94d33c92
-- title:
--   Direct product $F_1 \otimes F_2$ of two reproducing-kernel classes
-- statement:
--   Let $F_1$, $F_2$ be complex Hilbert spaces of functions on a set $E$ with continuous point evaluations, and let $F'$ be such a space of functions on $E' = E \times E$. We say $F'$ is the **direct product** $F_1 \otimes F_2$ when it is the functional completion of the class of functions of the form
--
--   $$
--   f'(x_1, x_2) = \sum_{k=1}^{n} f_1^{(k)}(x_1)\, f_2^{(k)}(x_2), \qquad f_1^{(k)} \in F_1,\ f_2^{(k)} \in F_2,
--   $$
--
--   with the scalar product $(f', g')' = \sum_{k=1}^{n}\sum_{l=1}^{m} (f_1^{(k)}, g_1^{(l)})_1 (f_2^{(k)}, g_2^{(l)})_2$. Concretely:
--
--   1. for $f_1 \in F_1$ and $f_2 \in F_2$, the function $(x_1, x_2) \mapsto f_1(x_1) f_2(x_2)$ belongs to $F'$;
--   2. the scalar product of two such products is $(f_1 \otimes f_2, g_1 \otimes g_2)' = (f_1, g_1)_1 (f_2, g_2)_2$;
--   3. finite sums of such products are dense in $F'$.
--
--   By sesquilinearity, property 2 gives the scalar product above on all finite sums; since $F'$ has continuous point evaluations and these sums are dense in it, the uniqueness of the functional completion (§4) identifies $F'$, functions and norm, with the paper's $F_1 \otimes F_2$.
--
--   **Formalization Note** The direct product is characterized by its elementary products and its scalar product, never through its kernel: its reproducing kernel is the content of §8, Theorem I. Mathlib's $\langle u, v\rangle$ is Aronszajn's $(v, u)$; the identity in 2 reads $\langle f_1 \otimes f_2, g_1 \otimes g_2\rangle = \langle f_1, g_1\rangle \langle f_2, g_2\rangle$ in either convention.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 358, §8, (1)–(2); p. 361, §8

import Mathlib

open scoped InnerProductSpace

namespace AronszajnRK.Product

/-- **The direct product `F′ = F₁ ⊗ F₂`** (N. Aronszajn, *Theory of Reproducing Kernels*,
Trans. Amer. Math. Soc. 68 (1950), §8, (1)–(2), p. 358, PDF p. 22, and p. 361, PDF p. 25).
`H₁`, `H₂` are complex RKHSs of functions on `X`, and `H'` is a complex RKHS of functions on
`X × X`. `IsDirectProduct H₁ H₂ H'` says that `H'` is the functional completion of the class of
functions of type (1), `f′(x₁, x₂) = Σₖ f₁⁽ᵏ⁾(x₁) f₂⁽ᵏ⁾(x₂)`, with the scalar product (2):
1. for `f₁ ∈ H₁`, `f₂ ∈ H₂` the function `(x₁, x₂) ↦ f₁(x₁) f₂(x₂)` belongs to `H'`;
2. the scalar product of two such products is the product of the scalar products,
   `⟪f₁ ⊗ f₂, g₁ ⊗ g₂⟫ = ⟪f₁, g₁⟫₁ ⟪f₂, g₂⟫₂` (this is (2) on one-term sums; Mathlib's
   `⟪u, v⟫_ℂ` is Aronszajn's `(v, u)`, and the identity has the same form in both conventions);
3. the linear span of these products (the functions of type (1)) is dense in `H'`.
By sesquilinearity, 2 gives (2) on all functions of type (1); since `H'` is an RKHS in which
they are dense, the uniqueness of functional completion (§4) identifies `H'` with Aronszajn's
`F₁ ⊗ F₂`, functions and norm. -/
def IsDirectProduct {X : Type*} (H₁ H₂ H' : Type*)
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [RKHS ℂ H₁ X ℂ]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [RKHS ℂ H₂ X ℂ]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [RKHS ℂ H' (X × X) ℂ] : Prop :=
  (∀ (f₁ : H₁) (f₂ : H₂), ∃ u : H', ∀ p : X × X, u p = f₁ p.1 * f₂ p.2) ∧
  (∀ (f₁ g₁ : H₁) (f₂ g₂ : H₂) (u v : H'),
      (∀ p : X × X, u p = f₁ p.1 * f₂ p.2) → (∀ p : X × X, v p = g₁ p.1 * g₂ p.2) →
      ⟪u, v⟫_ℂ = ⟪f₁, g₁⟫_ℂ * ⟪f₂, g₂⟫_ℂ) ∧
  Dense (Submodule.span ℂ
      {u : H' | ∃ (f₁ : H₁) (f₂ : H₂), ∀ p : X × X, u p = f₁ p.1 * f₂ p.2} : Set H')

end AronszajnRK.Product



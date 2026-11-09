-- Prove2me | Definitions.Def_DerandSq_NCPoly
-- name    : DerandSq_NCPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:53:57.513018+00:00
-- url     : https://prove2.me/theorems/68c7a61e-c056-47df-8e5f-bac7550ca698
-- title:
--   Non-commutative $*$-polynomials with matrix coefficients
-- statement:
--   $M_D(\mathbb C) \otimes \mathbb C^*\langle x_i : i \in \iota\rangle$ is the space of **non-commutative $*$-polynomials with $D \times D$ matrix coefficients** in the variables $x_i$:
--   $$
--   P = \sum_{w} A_w \otimes w ,
--   $$
--   a finite sum over words $w$ in the letters $x_i, x_i^*$ with coefficients $A_w \in M_D(\mathbb C)$.
--
--   **Formalization Note** A polynomial is a finitely supported map from words (`FreeMonoid (ι ⊕ ι)`, letter `Sum.inl i` = $x_i$, `Sum.inr i` = $x_i^*$) to $D \times D$ matrices, as in the published `StrongConv.NCPoly` (there for $\iota = $ `Fin d`). Theorem 2.14's second display uses $\iota = $ `Fin r ⊕ Fin s` for the variables $x_1, \dots, x_r, y_1, \dots, y_s$.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Theorem 2.14, pp.12–13

import Mathlib

namespace DerandSq

/-- `M_D(ℂ) ⊗ ℂ*⟨x_i : i ∈ ι⟩`: non-commutative ∗-polynomials with `D × D` complex matrix
coefficients in the variables `x_i` (Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), Theorem 2.14, pp.12–13), `P = ∑_w A_w ⊗ w`.

**Formalization Note** A polynomial is a finitely supported map from words in the letters
`Sum.inl i` (standing for `x_i`) and `Sum.inr i` (standing for `x_i*`) to `D × D` matrices, as in
the published `StrongConv.NCPoly` (there for `ι = Fin d`). For Theorem 2.14's second display the
variables are `ι = Fin r ⊕ Fin s` (`x_1, …, x_r, y_1, …, y_s`). -/
abbrev NCPoly (D : ℕ) (ι : Type*) := FreeMonoid (ι ⊕ ι) →₀ Matrix (Fin D) (Fin D) ℂ

end DerandSq



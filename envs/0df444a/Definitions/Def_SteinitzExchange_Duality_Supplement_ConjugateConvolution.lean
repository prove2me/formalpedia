-- Prove2me | Definitions.Def_SteinitzExchange_Duality_Supplement_ConjugateConvolution
-- name    : SteinitzExchange_Duality_Supplement_ConjugateConvolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:24:12.844686+00:00
-- url     : https://prove2.me/theorems/9780830d-9ee1-47cc-b01b-4862ea8c2474
-- title:
--   Real and integer supremum convolutions $\omega_1^\circ\,\square_{\mathbb R}\,\omega_2^\circ$ and $\omega_1^\circ\,\square_{\mathbb Z}\,\omega_2^\circ$ of concave conjugates
-- statement:
--   Let $V$ be a finite set, $B_1,B_2\subseteq\mathbb Z^V$ finite nonempty, and $\omega_i:B_i\to\mathbb R$ with concave conjugates $\omega_i^\circ(p)=\min\{\langle p,x\rangle-\omega_i(x)\mid x\in B_i\}$ ($p\in\mathbb R^V$). The **real convolution** of the conjugates is
--   $$(\omega_1^\circ\,\square_{\mathbb R}\,\omega_2^\circ)(p)=\sup\{\omega_1^\circ(p_1)+\omega_2^\circ(p_2)\mid p_1+p_2=p,\ p_1,p_2\in\mathbb R^V\}\qquad(p\in\mathbb R^V),$$
--   and the **integer convolution** is
--   $$(\omega_1^\circ\,\square_{\mathbb Z}\,\omega_2^\circ)(p)=\sup\{\omega_1^\circ(p_1)+\omega_2^\circ(p_2)\mid p_1+p_2=p,\ p_1,p_2\in\mathbb Z^V\}\qquad(p\in\mathbb Z^V).$$
--
--   These are the right-hand sides of the conjugacy identities (6.18) and (6.19) of Theorem 6.11.
--
--   **Formalization Note.** Both suprema are taken in `EReal`, so an unbounded family has value $+\infty$ and no junk value arises; the families are never empty ($p_1=p$, $p_2=0$). The page writes "$p_1\in\mathbf R,\ p_2\in\mathbf R$" (resp. $\mathbf Z$); since $p_1+p_2=p\in\mathbb R^V$, the splitting vectors range over $\mathbb R^V$ (resp. $\mathbb Z^V$). The conjugates are the published `concaveConj` with respect to $B_1$ and $B_2$.
--
--   The input conjugates use the published real-valued interface: for an empty base its value is the default zero, outside the source domain. All conjugacy identities here assume nonempty bases.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 303, Section 6.4 (definitions of ω₁° □_R ω₂° and ω₁° □_Z ω₂°)

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Conjugate

namespace SteinitzExchange.Duality.Supplement

/-- The real supremum convolution of concave conjugates (Murota 1996, p. 303, §6.4):
`(ω₁° □_ℝ ω₂°)(p) = sup{ω₁°(p₁) + ω₂°(p₂) | p₁ + p₂ = p, p₁, p₂ ∈ ℝ^V}`, where `ωᵢ°` is the
concave conjugate of `ωᵢ` with respect to `Bᵢ` (Eq. (4.1)). The supremum is taken in `EReal`,
so an unbounded family has value `⊤ = +∞` and no junk value arises; the family is never empty
(`p₁ = p`, `p₂ = 0`). -/
noncomputable def realConjConv {V : Type*} [Fintype V] (B₁ : Finset (V → ℤ))
    (ω₁ : (V → ℤ) → ℝ) (B₂ : Finset (V → ℤ)) (ω₂ : (V → ℤ) → ℝ) (p : V → ℝ) : EReal :=
  ⨆ (p₁ : V → ℝ) (p₂ : V → ℝ) (_ : p₁ + p₂ = p),
    ((concaveConj B₁ ω₁ p₁ + concaveConj B₂ ω₂ p₂ : ℝ) : EReal)

/-- The integer supremum convolution of concave conjugates (Murota 1996, p. 303, §6.4):
`(ω₁° □_ℤ ω₂°)(p) = sup{ω₁°(p₁) + ω₂°(p₂) | p₁ + p₂ = p, p₁, p₂ ∈ ℤ^V}` for `p ∈ ℤ^V`.
The supremum is taken in `EReal` (unbounded family ↦ `⊤`); the family is never empty. -/
noncomputable def intConjConv {V : Type*} [Fintype V] (B₁ : Finset (V → ℤ))
    (ω₁ : (V → ℤ) → ℝ) (B₂ : Finset (V → ℤ)) (ω₂ : (V → ℤ) → ℝ) (p : V → ℤ) : EReal :=
  ⨆ (p₁ : V → ℤ) (p₂ : V → ℤ) (_ : p₁ + p₂ = p),
    ((concaveConj B₁ ω₁ (toReal p₁) + concaveConj B₂ ω₂ (toReal p₂) : ℝ) : EReal)

end SteinitzExchange.Duality.Supplement



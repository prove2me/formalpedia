-- Prove2me | Definitions.Def_BosonicLearn_coherentVector
-- name    : BosonicLearn_coherentVector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:12.972193+00:00
-- url     : https://prove2.me/theorems/c11b555c-8972-40d4-86d7-94f401cc20c4
-- title:
--   Coherent vector $|\alpha(\beta)\rangle$ in the Fock basis
-- statement:
--   For $\beta=(\beta_{q,1},\dots,\beta_{q,n},\beta_{p,1},\dots,\beta_{p,n})\in\mathbb R^{2n}$ let $\alpha_j=(\beta_{q,j}+i\beta_{p,j})/\sqrt2$. The coherent vector with amplitudes $\alpha$ has Fock coefficients
--
--   $$c(\beta)_m=\prod_{j=1}^n e^{-|\alpha_j|^2/2}\,\frac{\alpha_j^{m_j}}{\sqrt{m_j!}}\qquad(m\in\mathbb N^n).$$
--
--   It is the eigenvector of every $\hat a_j$ with eigenvalue $\alpha_j$, and its quadrature means are $\langle\hat q_j\rangle=\beta_{q,j}$, $\langle\hat p_j\rangle=\beta_{p,j}$. Heterodyne detection projects onto these vectors.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, p. 5; Eq. (207), p. 61

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace BosonicLearn

/-- **Coherent vector `|α(β)⟩` in the Fock basis.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, p. 5: "|α⟩ is the coherent state (i.e., eigenstates of {â_j})"; heterodyne outcomes are points
`β ∈ ℝ²ⁿ` in the paper's grouped quadrature coordinates (Eq. (2), p. 4, and Eq. (207), p. 61).

For `β = (β_{q,1},…,β_{q,n},β_{p,1},…,β_{p,n})` put `α_j = (β_{q,j} + i β_{p,j})/√2`. The coherent vector has Fock
coefficients
$$c(β)_m = \prod_j e^{-|α_j|^2/2}\, \frac{α_j^{m_j}}{\sqrt{m_j!}} .$$

**Formalization Note.** With `q̂ = (â+â†)/√2`, `p̂ = (â−â†)/(i√2)`, the coherent state of amplitude `α_j` has
`⟨q̂_j⟩ = √2 Re α_j = β_{q,j}` and `⟨p̂_j⟩ = √2 Im α_j = β_{p,j}`. -/
noncomputable def coherentVector {n : ℕ} (β : Fin n ⊕ Fin n → ℝ) : Occupation (Fin n) → ℂ :=
  fun m => ∏ j, ((Real.exp (-(β (Sum.inl j) ^ 2 + β (Sum.inr j) ^ 2) / 4) : ℝ) : ℂ) *
    ((β (Sum.inl j) : ℂ) + Complex.I * (β (Sum.inr j) : ℂ)) ^ (m j) /
      ((Real.sqrt 2 : ℂ) ^ (m j) * (Real.sqrt (Nat.factorial (m j)) : ℂ))

end BosonicLearn



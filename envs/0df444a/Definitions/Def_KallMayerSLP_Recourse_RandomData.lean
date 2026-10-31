-- Prove2me | Definitions.Def_KallMayerSLP_Recourse_RandomData
-- name    : KallMayerSLP_Recourse_RandomData
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:11:35.490289+00:00
-- url     : https://prove2.me/theorems/ff991182-f503-4b5c-9a7b-9e4639c4967c
-- title:
--   Second-stage data $T(\xi),h(\xi),q(\xi)$ affine in $\xi$, eq. (2.1)
-- statement:
--   In the two-stage stochastic linear program the second-stage data depend affinely on a random vector $\xi\in\mathbb R^r$. With deterministic arrays $T,T^j\in\mathbb R^{m_2\times n_1}$, $h,h^j\in\mathbb R^{m_2}$ and $q,q^j\in\mathbb R^{n_2}$ ($j=1,\dots,r$),
--
--   $$
--   T(\xi)=T+\sum_{j=1}^r T^j\xi_j,\qquad h(\xi)=h+\sum_{j=1}^r h^j\xi_j,\qquad q(\xi)=q+\sum_{j=1}^r q^j\xi_j .
--   $$
--
--   These are the technology matrix, the right-hand side and the cost vector of the second-stage (recourse) problem. The recourse matrix is fixed, $W(\xi)\equiv W$ (fixed recourse), so it is not part of this structure; every statement of the mission takes one deterministic matrix $W\in\mathbb R^{m_2\times n_2}$.
--
--   **Formalization Note** The structure stores the coefficients $T,T^j,h,h^j,q,q^j$ as `T0, Tj, h0, hj, q0, qj`; `D.T ξ`, `D.h ξ`, `D.q ξ` are the affine maps above. Vectors are `Fin k → ℝ`.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, eq. (2.1), p.199 (PDF 208); fixed recourse W(·) ≡ W, p.200 (PDF 209)

import Mathlib

namespace KallMayerSLP.Recourse

/-- The random second-stage data of the two-stage SLP, affine in the random vector `ξ ∈ ℝʳ`
(Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, eq. (2.1), p.199, PDF 208):

`T(ξ) = T + Σⱼ Tʲ ξⱼ`, `h(ξ) = h + Σⱼ hʲ ξⱼ`, `q(ξ) = q + Σⱼ qʲ ξⱼ`,

with deterministic `T, Tʲ ∈ ℝ^{m₂×n₁}`, `h, hʲ ∈ ℝ^{m₂}`, `q, qʲ ∈ ℝ^{n₂}`.

**Formalization Note.** The fields `T0, Tj, h0, hj, q0, qj` are the book's `T, Tʲ, h, hʲ, q, qʲ`;
the indices `j = 1, …, r` are `Fin r`. The recourse matrix is *fixed* (`W(ξ) ≡ W`, p.200: "instead
of (2.1) we shall restrict ourselves to `W(·) ≡ W`"), so it is not a field here: every statement takes
one deterministic matrix `W`. The first-stage data `A, b, c` are not needed by the statements of
§2.1 that use this structure. -/
structure RandomData (m₂ n₁ n₂ r : ℕ) where
  /-- `T ∈ ℝ^{m₂×n₁}` -/
  T0 : Matrix (Fin m₂) (Fin n₁) ℝ
  /-- `Tʲ ∈ ℝ^{m₂×n₁}`, `j = 1, …, r` -/
  Tj : Fin r → Matrix (Fin m₂) (Fin n₁) ℝ
  /-- `h ∈ ℝ^{m₂}` -/
  h0 : Fin m₂ → ℝ
  /-- `hʲ ∈ ℝ^{m₂}`, `j = 1, …, r` -/
  hj : Fin r → Fin m₂ → ℝ
  /-- `q ∈ ℝ^{n₂}` -/
  q0 : Fin n₂ → ℝ
  /-- `qʲ ∈ ℝ^{n₂}`, `j = 1, …, r` -/
  qj : Fin r → Fin n₂ → ℝ

namespace RandomData

variable {m₂ n₁ n₂ r : ℕ}

/-- `T(ξ) = T + Σ_{j=1}^r Tʲ ξⱼ`, eq. (2.1). -/
def T (D : RandomData m₂ n₁ n₂ r) (ξ : Fin r → ℝ) : Matrix (Fin m₂) (Fin n₁) ℝ :=
  D.T0 + ∑ j, ξ j • D.Tj j

/-- `h(ξ) = h + Σ_{j=1}^r hʲ ξⱼ`, eq. (2.1). -/
def h (D : RandomData m₂ n₁ n₂ r) (ξ : Fin r → ℝ) : Fin m₂ → ℝ :=
  D.h0 + ∑ j, ξ j • D.hj j

/-- `q(ξ) = q + Σ_{j=1}^r qʲ ξⱼ`, eq. (2.1). -/
def q (D : RandomData m₂ n₁ n₂ r) (ξ : Fin r → ℝ) : Fin n₂ → ℝ :=
  D.q0 + ∑ j, ξ j • D.qj j

end RandomData

end KallMayerSLP.Recourse



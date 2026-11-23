-- Prove2me | Definitions.Def_VBSDP_Duality_Supplement_IsNewtonDirection
-- name    : VBSDP_Duality_Supplement_IsNewtonDirection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:06:29.932645+00:00
-- url     : https://prove2.me/theorems/d6d6a57a-fbab-4b61-bf7f-741e08f6036f
-- title:
--   (48), p. 72 — the Newton direction δxᴺ for the barrier ϕ
-- statement:
--   Let $x$ satisfy $F(x)>0$ and write $F=F(x)$. The **Newton direction** $\delta x^N$ at $x$ is a vector minimizing the second-order expansion of $\phi(x+v)-\phi(x)$ over all $v\in\mathbb R^m$:
--
--   $$\delta x^N=\operatorname*{argmin}_{v\in\mathbb R^m}\left(-\operatorname{Tr}F^{-1}\Big(\sum_{i=1}^mv_iF_i\Big)+\frac12\operatorname{Tr}\Big(\sum_{i=1}^mv_iF_i\Big)F^{-1}\Big(\sum_{j=1}^mv_jF_j\Big)F^{-1}\right),$$
--
--   the first form of (48); the page rewrites it as the least-squares problem $\min_v\|-I+\sum_iv_iF^{-1/2}F_iF^{-1/2}\|_F$.
--
--   **Formalization Note** The predicate says that $\delta x^N$ minimizes the quadratic of the first line of (48) over all of $\mathbb R^m$ (the later lines are equal reformulations). $F^{-1}$ is Mathlib's matrix inverse, the true inverse when $F(x)>0$. Indices are zero-based.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 72 (PDF p. 24), (48); https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_Supplement_barrier

namespace VBSDP.Duality.Supplement

/-- The Newton direction (48), p. 72: with `F = F(x)`, `δxᴺ` minimizes over all `v ∈ ℝᵐ`
the second-order expansion
`−Tr F⁻¹(Σᵢ vᵢFᵢ) + ½ Tr (Σᵢ vᵢFᵢ) F⁻¹ (Σⱼ vⱼFⱼ) F⁻¹` of `ϕ(x + v) − ϕ(x)`. -/
noncomputable def IsNewtonDirection {m n : ℕ} (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) (x δx : Fin m → ℝ) : Prop :=
  let G := (VBSDP.Duality.lmi F₀ F x)⁻¹
  let q : (Fin m → ℝ) → ℝ := fun v =>
    -(G * ∑ i, v i • F i).trace +
      (1 / 2 : ℝ) * ((∑ i, v i • F i) * G * (∑ j, v j • F j) * G).trace
  ∀ v : Fin m → ℝ, q δx ≤ q v

end VBSDP.Duality.Supplement



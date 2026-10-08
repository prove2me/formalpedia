-- Prove2me | Definitions.Def_LogBarrierIPM_Iterations_TropicalSegment
-- name    : LogBarrierIPM_Iterations_TropicalSegment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T13:45:36.802388+00:00
-- url     : https://prove2.me/theorems/0f11c9d2-199e-4f1c-b4ea-0e1775a6b21f
-- title:
--   Tropical segments $\mathsf{tsegm}(u,v)$ in $\mathbb T^d$
-- statement:
--   Let $\mathbb T=\mathbb R\cup\{-\infty\}$ be the tropical (max-plus) semifield, with $a\oplus b=\max(a,b)$ and $a\odot b=a+b$ (so $-\infty\odot a=-\infty$); operations on $\mathbb T^d$ are coordinatewise. The **tropical segment** between $u,v\in\mathbb T^d$ is
--   $$\mathsf{tsegm}(u,v)=\{\lambda\odot u\oplus\mu\odot v:\ \lambda,\mu\in\mathbb T,\ \lambda\oplus\mu=0\},$$
--   that is, the points with coordinates $\max(\lambda+u_i,\mu+v_i)$ for $\max(\lambda,\mu)=0$. For a real parameter $\mu$ we also name the point $u\oplus(\mu\odot v)$, with coordinates $\max(u_i,\mu+v_i)$.
--
--   Tropical segments are the tropical analogue of line segments; the paper compares them with the images under $\log_t$ of ordinary segments, which is how the iterates of an interior point method are related to the tropical central path.
--
--   **Formalization Note** $\mathbb T$ is `WithBot ℝ`, with $\bot$ playing $-\infty$ and the tropical unit $0$ the real number $0$.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 9 (tropical segment), p. 10 (proof of Lemma 5, u ⊕ (µ ⊙ v))

import Mathlib

namespace LogBarrierIPM.Iterations

/-- The tropical segment (p. 9) between `u, v ∈ 𝕋^d`, `𝕋 = ℝ ∪ {−∞}` (`WithBot ℝ`):
`tsegm(u, v) = {λ ⊙ u ⊕ μ ⊙ v : λ, μ ∈ 𝕋, λ ⊕ μ = 0}`, where `⊕ = max` and `⊙ = +`
coordinatewise (`−∞ + a = −∞`). -/
def tsegm {d : ℕ} (u v : Fin d → WithBot ℝ) : Set (Fin d → WithBot ℝ) :=
  {x | ∃ la mu : WithBot ℝ, max la mu = 0 ∧ x = fun i => max (la + u i) (mu + v i)}

/-- The point `u ⊕ (μ ⊙ v)` of `𝕋^d` for a real parameter `μ`: coordinatewise
`max(u_i, μ + v_i)`. -/
def tsegParam {d : ℕ} (u v : Fin d → WithBot ℝ) (mu : ℝ) : Fin d → WithBot ℝ :=
  fun i => max (u i) ((mu : WithBot ℝ) + v i)

end LogBarrierIPM.Iterations



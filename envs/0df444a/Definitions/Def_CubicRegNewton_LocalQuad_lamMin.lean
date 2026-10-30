-- Prove2me | Definitions.Def_CubicRegNewton_LocalQuad_lamMin
-- name    : CubicRegNewton_LocalQuad_lamMin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:25:21.585711+00:00
-- url     : https://prove2.me/theorems/a24fe0c4-f33e-44a5-a41f-7ebd095a22d8
-- title:
--   Least eigenvalue $\lambda_n(H)$ as a Rayleigh infimum
-- statement:
--   For a linear operator $H$ on $\mathbb R^n$,
--
--   $$
--   \lambda_n(H)=\inf_{\|u\|=1}\langle Hu,u\rangle .
--   $$
--
--   For symmetric $H$ and $n\ge1$ this is the least eigenvalue of $H$, the quantity $\lambda_n(H)$ of the paper's notation, where the eigenvalues are numbered $\lambda_1(H)\ge\dots\ge\lambda_n(H)$. It is used at the Hessians $f''(x)$, $x\in F$.
--
--   **Formalization Note** The infimum is a real infimum over the unit sphere, on which $\langle Hu,u\rangle$ is bounded. For $n=0$ the sphere is empty and the value is $0$.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, doi:10.1007/s10107-006-0706-8, Notation, p. 180 (PDF p. 4)

import Mathlib

open scoped InnerProductSpace

namespace CubicRegNewton.LocalQuad

/-- **The least eigenvalue λₙ(H).**
Nesterov & Polyak, *Cubic regularization of Newton method and its global performance*,
Math. Program. Ser. A 108 (2006) 177–205, Notation, p. 180: "For a symmetric n × n matrix H, its
spectrum is denoted by {λi(H)}ⁿᵢ₌₁. We assume that the eigenvalues are numbered in decreasing order:
λ1(H) ≥ . . . ≥ λn(H)."

`lamMin H` is the infimum of the Rayleigh quotient `⟪H u, u⟫` over unit vectors `u`.

**Formalization Note.** Reading 5: for a symmetric (self-adjoint) `H` on ℝⁿ with `n ≥ 1` the
Rayleigh infimum is the least eigenvalue `λₙ(H)`; it is used only at Hessians `f''(x)`, `x ∈ F`,
which are symmetric under the standing assumptions. The set `{⟪H u, u⟫ | ‖u‖ = 1}` is bounded, so
the real infimum is not a junk value; for `n = 0` the unit sphere is empty and `lamMin H = 0`. -/
noncomputable def lamMin {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨅ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ⟪H u, u⟫_ℝ

end CubicRegNewton.LocalQuad



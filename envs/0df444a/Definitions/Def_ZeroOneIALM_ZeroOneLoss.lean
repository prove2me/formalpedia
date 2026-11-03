-- Prove2me | Definitions.Def_ZeroOneIALM_ZeroOneLoss
-- name    : ZeroOneIALM_ZeroOneLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:41.245592+00:00
-- url     : https://prove2.me/theorems/4bb46ce4-0600-4f32-a529-f67efdc490cf
-- title:
--   The zero-one loss $\ell_{0/1}$ and the count $\|u_+\|_0$
-- statement:
--   The **zero-one loss** is the function $\ell_{0/1}:\mathbb R\to\mathbb R$ with $\ell_{0/1}(t)=1$ for $t>0$ and $\ell_{0/1}(t)=0$ for $t\le 0$.
--
--   For $u\in\mathbb R^n$, write $u_+:=(\max\{0,u_1\},\dots,\max\{0,u_n\})^\top$. Then $\|u_+\|_0$ is the number of strictly positive components of $u$, and
--   $$
--   \|u_+\|_0=\sum_{i=1}^n\ell_{0/1}(u_i).
--   $$
--
--   This is the discontinuous term of the zero-one composite problem. It counts positive entries, not nonzero entries.
--
--   **Formalization Note** The count is defined by the sum above and is real-valued, since it is always multiplied by $\lambda$ and added to $f$.
-- source:
--   Zhang & Xiu, Global Convergence of Inexact Augmented Lagrangian Method for Zero-One Composite Optimization, arXiv:2112.00440v1, p.1

import Mathlib

namespace ZeroOneIALM

/-- The zero-one loss `ℓ_{0/1}` of Zhang & Xiu, Global Convergence of Inexact Augmented Lagrangian
Method for Zero-One Composite Optimization, arXiv:2112.00440v1, p.1: `ℓ_{0/1}(t) = 1` for `t > 0`
and `ℓ_{0/1}(t) = 0` for `t ≤ 0`. -/
noncomputable def zeroOneLoss (t : ℝ) : ℝ := if 0 < t then 1 else 0

/-- `‖u₊‖₀` of arXiv:2112.00440v1, p.1: the number of positive components of `u`, computed by the
paper's identity `‖u₊‖₀ = ∑ᵢ ℓ_{0/1}(uᵢ)`.

**Formalization Note.** The value is a real number, not a natural number, because it is multiplied
by `λ` and added to `f` everywhere it occurs. `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def posCount {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, zeroOneLoss (u i)

end ZeroOneIALM



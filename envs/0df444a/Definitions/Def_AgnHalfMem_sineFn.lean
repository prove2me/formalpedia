-- Prove2me | Definitions.Def_AgnHalfMem_sineFn
-- name    : AgnHalfMem_sineFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:12:46.867021+00:00
-- url     : https://prove2.me/theorems/a3a3a7b4-b630-4e80-9df6-7fcdeeb2d00b
-- title:
--   The sine functions $f_v(z)=\sin(\tau\langle v,z\rangle)$ and the Gaussian $N(0,I_s/s)$
-- statement:
--   For $\tau\in\mathbb R$ and $v\in\mathbb R^s$, the **sine function** $f_v:\mathbb R^s\to[-1,1]$ is
--   $$
--   f_v(z)=\sin(\tau\langle v,z\rangle),\qquad \langle v,z\rangle=\sum_{j=1}^s v_jz_j .
--   $$
--   The random direction $v$ is drawn from the normalized Gaussian $N(0,\tfrac1s I_s)$, the product of $s$ centred normal laws of variance $1/s$. These functions are the columns of the extractor matrix in the proof of Lemma 4.7.
--
--   **Formalization Note** Mathlib's `gaussianReal m v` takes the variance $v\in\mathbb R_{\ge0}$.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), proof of Lemma 4.7, pp.13–14

import Mathlib
import Definitions.Def_AgnHalfMem_halfspace

open MeasureTheory ProbabilityTheory

namespace AgnHalfMem

/-- **The sine functions `f_v` and the Gaussian `N(0, I_s/s)`.** S. Garg, T. Jadhav,
*Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript,
PDF sha256 386bc9b3…43f84d5), proof of Lemma 4.7, p.13: "For a vector v ∈ ℝ^s, define
f_v : ℝ^s → [−1, 1] as f_v(z) = sin(τ⟨v, z⟩)"; p.14: "v drawn from normalized standard
multivariate gaussian, that is, N(0, (1/s) I_s)".

`sineFn τ v z = sin(τ ⟨v, z⟩)` with the non-normalized inner product of §4.3, and `gaussVec s` is
`N(0, I_s/s)`, the product of `s` centred Gaussians of variance `1/s`.

**Formalization Note.** Vectors are `Fin s → ℝ`. Mathlib's `gaussianReal m v` takes the variance
`v : ℝ≥0`. -/
noncomputable def sineFn {s : ℕ} (τ : ℝ) (v z : Fin s → ℝ) : ℝ :=
  Real.sin (τ * dot v z)

/-- `N(0, I_s/s)` on `ℝ^s` (p.14). -/
noncomputable def gaussVec (s : ℕ) : Measure (Fin s → ℝ) :=
  Measure.pi fun _ : Fin s => gaussianReal 0 ((s : NNReal)⁻¹)

end AgnHalfMem



-- Prove2me | Definitions.Def_SchattenSketch_Main_HardModel
-- name    : SchattenSketch_Main_HardModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:56:47.466757+00:00
-- url     : https://prove2.me/theorems/c52e24d0-5ea4-42a9-9bb4-e4e44db33058
-- title:
--   The rotated spectral matrix $F=\sqrt n\,UDV^\top$ of (4.18) and the standard Gaussian law $N(0,I_k)$
-- statement:
--   For orthogonal matrices $U,V\in O_n=\{Q\in\mathbb R^{n\times n}:Q^\top Q=I_n\}$ and a vector $d\in\mathbb R^n$, the **rotated spectral matrix** of the paper's hard instances is
--   $$F=\sqrt n\;U\,\mathrm{diag}(d_1,\dots,d_n)\,V^\top .$$
--   In §4 the diagonal entries are square roots of particle positions, $U,V$ are independent and Haar distributed on $O_n$, and the hard input is $X=aF+\sigma Z$ with an independent standard Gaussian matrix $Z$.
--
--   The **standard Gaussian law** $N(0,I_k)$ on $\mathbb R^k$ is the product of $k$ standard normal laws $N(0,1)$.
--
--   **Formalization Note.** `rotDiag U V d` takes `U V : FourierRankQLB.Od n` (the published orthogonal group, with its Haar probability measure `haarO n`). `stdGaussian k` is `Measure.pi` of `gaussianReal 0 1`; it is a probability measure.
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 17, (4.18)–(4.19); p. 18, (4.21)

import Mathlib
import Definitions.Def_FourierRankQLB_Od

open MeasureTheory ProbabilityTheory

namespace SchattenSketch.Main

/-- The rotated spectral matrix `F = √n · U D Vᵀ` of (4.18) (Yang, p. 17), for orthogonal
`U, V ∈ O_n` and the diagonal matrix `D = diag(d₁, …, dₙ)`. -/
noncomputable def rotDiag {n : ℕ} (U V : FourierRankQLB.Od n) (d : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Real.sqrt n • ((U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal d *
    (V : Matrix (Fin n) (Fin n) ℝ).transpose)

/-- The standard Gaussian law `N(0, I_k)` on `ℝ^k`: independent `N(0, 1)` coordinates. -/
noncomputable def stdGaussian (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ : Fin k => gaussianReal 0 1

instance stdGaussian_isProbabilityMeasure (k : ℕ) : IsProbabilityMeasure (stdGaussian k) := by
  unfold stdGaussian; infer_instance

end SchattenSketch.Main



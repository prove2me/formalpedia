-- Prove2me | Definitions.Def_CaiFourierSparse_Learning_SparseFFT
-- name    : CaiFourierSparse_Learning_SparseFFT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:11:24.519008+00:00
-- url     : https://prove2.me/theorems/4107a7e3-8776-4d6a-b854-c45154771fd2
-- title:
--   The discrete Fourier transform and sparse outputs
-- statement:
--   For $v\in\mathbb C^m$, $\hat v[f]=\sum_{j\in[m]}v[j]e^{-2\pi ifj/m}$ (unnormalized; `dft`). A sparse vector of $\mathbb C^m$ is written as a list of (index, value) pairs (`encSparse`); the vector it describes adds the values of each index (`sparseVec`). $\|v\|_2=(\sum_j|v_j|^2)^{1/2}$ (`l2norm`).
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), §2 (DFT convention) and Lemma 5.5, printed pp. 7, 27 (PDF pp. 9, 29)

import Mathlib

namespace CaiFourierSparse.Learning

/-! # The discrete Fourier transform and sparse outputs (Cai–Chen–Shao–Wang, §2, Lemma 5.5)

For `v ∈ ℂ^m`, `v̂[f] = ∑_{j ∈ [m]} v[j] e^{-2π i f j / m}` (unnormalized; the inverse carries
`1/m`). A sparse vector of `ℂ^m` is output as a list of (index, value) pairs; its length is
bounded by the running time of the program that writes it. -/

/-- The unnormalized DFT `v̂[f] = ∑_{j<m} v[j] e^{-2π i f j/m}`. -/
noncomputable def dft {m : ℕ} (v : Fin m → ℂ) (f : Fin m) : ℂ :=
  ∑ j : Fin m, v j * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (f : ℂ) * (j : ℂ) / m))

/-- Output encoding of a sparse vector given by (index, value) pairs. -/
def encSparse {m : ℕ} (L : List (Fin m × ℂ)) : List ℂ :=
  L.flatMap fun p => [((p.1 : ℕ) : ℂ), p.2]

/-- The vector of `ℂ^m` described by a list of (index, value) pairs (values of a repeated index
are added). -/
def sparseVec {m : ℕ} (L : List (Fin m × ℂ)) (j : Fin m) : ℂ :=
  ((L.filter fun p => p.1 = j).map Prod.snd).sum

/-- The Euclidean norm `‖v‖₂` on `ℂ^m`. -/
noncomputable def l2norm {m : ℕ} (v : Fin m → ℂ) : ℝ := Real.sqrt (∑ j, ‖v j‖ ^ 2)

end CaiFourierSparse.Learning



-- Prove2me | Definitions.Def_SparseTensorInj_Certify_GaussianSeries
-- name    : SparseTensorInj_Certify_GaussianSeries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:37:17.514177+00:00
-- url     : https://prove2.me/theorems/5d1f4289-bf8f-4455-8311-70fd08dbb330
-- title:
--   Gaussian matrix series $W=\sum_jg_jB_j$ and its parameters $\sigma_G$, $\nu_G$ (Definition 84)
-- statement:
--   For independent standard Gaussians $g_1,\dots,g_N$ and deterministic $B_1,\dots,B_N\in\mathbb R^{d\times d}$, the **Gaussian matrix series** is $W=\sum_{j=1}^Ng_jB_j$, with parameters
--   $$\sigma_G^2=\max\Big\{\Big\|\sum_jB_jB_j^\top\Big\|_{\mathrm{op}},\Big\|\sum_jB_j^\top B_j\Big\|_{\mathrm{op}}\Big\},\qquad \nu_G^2=\|\mathrm{Cov}(\mathrm{vec}(W))\|_{\mathrm{op}},$$
--   where $\mathrm{vec}(W)$ is the vector of entries of $W$. Proposition 85 bounds the moments of $\|W\|_{\mathrm{op}}$ in terms of them.
--
--   **Formalization Note.** `gaussSeries B g` is $W$ at the Gaussian vector $g$. Since the $g_j$ are i.i.d. $N(0,1)$, $\mathrm{Cov}(\mathrm{vec}(W))[(a,b),(c,e)]=\sum_jB_j[a,b]B_j[c,e]$; `covVec B` is this matrix, and `nuG B` its operator norm's square root.
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), pp. 47–48, Definition 84

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_Tensor

namespace SparseTensorInj.Certify

/-- The Gaussian matrix series `W = Σ_{j=1}^N g_j B_j` (Definition 84, p. 47) at the Gaussian
vector `g = (g_1, …, g_N)`, for deterministic `B_1, …, B_N ∈ ℝ^{d × d}`. -/
def gaussSeries {N d : ℕ} (B : Fin N → Matrix (Fin d) (Fin d) ℝ) (g : Fin N → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∑ j : Fin N, g j • B j

/-- `σ_G = (max {‖Σ_j B_j B_j^⊤‖_op, ‖Σ_j B_j^⊤ B_j‖_op})^{1/2}` (Definition 84, p. 48). -/
noncomputable def sigmaG {N d : ℕ} (B : Fin N → Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  Real.sqrt (max (opNorm (∑ j : Fin N, B j * (B j).transpose))
    (opNorm (∑ j : Fin N, (B j).transpose * B j)))

/-- The covariance matrix `Cov(vec(W))` of the entries of `W` when `g_1, …, g_N` are i.i.d.
`N(0, 1)`: `Cov[(a, b), (c, e)] = Σ_j B_j[a, b] B_j[c, e]`. -/
def covVec {N d : ℕ} (B : Fin N → Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℝ :=
  fun p p' => ∑ j : Fin N, B j p.1 p.2 * B j p'.1 p'.2

/-- `ν_G = ‖Cov(vec(W))‖_op^{1/2}` (Definition 84, p. 48). -/
noncomputable def nuG {N d : ℕ} (B : Fin N → Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  Real.sqrt (opNorm (covVec B))

end SparseTensorInj.Certify



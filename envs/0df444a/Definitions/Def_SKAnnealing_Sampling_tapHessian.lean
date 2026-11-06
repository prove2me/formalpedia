-- Prove2me | Definitions.Def_SKAnnealing_Sampling_tapHessian
-- name    : SKAnnealing_Sampling_tapHessian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:15:42.502147+00:00
-- url     : https://prove2.me/theorems/3712fc1b-3af8-46fe-8a30-d277c0001c81
-- title:
--   The TAP Hessian $K$ and the quantities $m$, $v_i$, $q_N$, $d_i$, $\lambda_i$, $f_i$ of Section 4
-- statement:
--   Let $\mu$ be a law on $\{\pm1\}^N$ (in Section 4, $\mu=\mu_t$ of Theorem 1.4) and $M=W+\frac\beta Nxx^\top$ **with its diagonal set to zero**. Write $\mathbf{Cov}=\mathbf{Cov}(\mu)$ and
--   $$m=\langle\sigma\rangle\ (m_i=\mathbf E_\mu\sigma_i),\qquad v_i=1-m_i^2,\qquad q_N=\frac{\|m\|^2}N .$$
--   The **TAP Hessian** (8) is
--   $$K=\mathrm{diag}(v_i^{-1})-\beta M+\beta^2(1-q_N)\,\mathrm{Id}-\frac{2\beta^2}Nmm^\top .$$
--   For each $i\in[N]$, with vectors indexed by $[N]\setminus\{i\}$,
--   $$d_i=\frac{\mathbf{Cov}_{i,-i}}{v_i},\qquad \lambda_i=\beta^2(1-q_N)-\beta\,d_i^\top M_{i,-i},\qquad f_i=(K\mathbf{Cov}-\mathrm{Id})_{i,-i}.$$
--
--   $K^{-1}$ is the paper's prediction for the covariance; Section 4 bounds $K\mathbf{Cov}-\mathrm{Id}$ and Section 5 bounds $K$ from below.
--
--   **Formalization Note** A vector indexed by $[N]\setminus\{i\}$ is a vector of $\mathbb R^N$ whose entry $i$ is $0$. $v_i>0$ for every full-support law, in particular for $\mu_t$.
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), display (8), p. 15; p. 16; p. 21

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean

open OAI.CriticalSK

namespace SKAnnealing.Sampling

/-- `M = W + (β/N) x xᵀ` with **zeroed diagonal**, as a symmetric `N × N` matrix built from the edges.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), p. 12 (`M := W + β xxᵀ/N`) and p. 15 ("the diagonal of M is zeroed out"). -/
noncomputable def plantedMatrix {N : ℕ} (β : ℝ) (W : Disorder N) (x : Spin N) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i k =>
    if h : i < k then W ⟨(i, k), h⟩ + β / N * spinValue (x i) * spinValue (x k)
    else if h' : k < i then W ⟨(k, i), h'⟩ + β / N * spinValue (x k) * spinValue (x i)
    else 0

/-- The magnetization `m = ⟨σ⟩` of a law `p`: `m_i = E_p[σ_i]`. -/
noncomputable def tapMean {N : ℕ} (p : Spin N → ℝ) : Fin N → ℝ :=
  fun i => lawMean p (fun y => spinValue (y i))

/-- `v_i = 1 − m_i^2`. -/
noncomputable def tapVar {N : ℕ} (p : Spin N → ℝ) (i : Fin N) : ℝ :=
  1 - tapMean p i ^ 2

/-- `q_N = ‖m‖²/N`. -/
noncomputable def overlapQ {N : ℕ} (p : Spin N → ℝ) : ℝ :=
  (∑ i, tapMean p i ^ 2) / N

/-- The **TAP Hessian** (8): `K = diag(v_i^{-1}) − β M + β²(1 − q_N) Id − (2β²/N) m mᵀ`, evaluated at the law
`p` (in Section 4, `p = µ_t` of Theorem 1.4 and `M = plantedMatrix β W x`).

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), display (8), p. 15; restated p. 21.

**Formalization Note** Encoded for any matrix `M` and law `p`; `v_i > 0` holds for every full-support law,
in particular for `µ_t`, so `v_i^{-1}` is the real inverse. -/
noncomputable def tapHessian {N : ℕ} (β : ℝ) (M : Matrix (Fin N) (Fin N) ℝ) (p : Spin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => (tapVar p i)⁻¹) - β • M + (β ^ 2 * (1 - overlapQ p)) • (1 : Matrix (Fin N) (Fin N) ℝ)
    - (2 * β ^ 2 / N) • Matrix.vecMulVec (tapMean p) (tapMean p)

/-- `d_i = Cov_{i,−i}/v_i`, as a vector of `ℝ^N` with entry `i` set to `0` (p. 16). -/
noncomputable def cavityD {N : ℕ} (p : Spin N → ℝ) (i : Fin N) : Fin N → ℝ :=
  fun j => if j = i then 0 else lawCov p i j / tapVar p i

/-- `λ_i = β²(1 − q_N) − β d_iᵀ M_{i,−i}` (p. 16). -/
noncomputable def cavityLam {N : ℕ} (β : ℝ) (M : Matrix (Fin N) (Fin N) ℝ) (p : Spin N → ℝ) (i : Fin N) : ℝ :=
  β ^ 2 * (1 - overlapQ p) - β * ∑ j, cavityD p i j * M i j

/-- `f_i = (K Cov − Id)_{i,−i}`, as a vector of `ℝ^N` with entry `i` set to `0` (p. 16). -/
noncomputable def residualRow {N : ℕ} (β : ℝ) (M : Matrix (Fin N) (Fin N) ℝ) (p : Spin N → ℝ) (i : Fin N) :
    Fin N → ℝ :=
  fun j => if j = i then 0 else (tapHessian β M p * lawCov p - 1) i j

end SKAnnealing.Sampling



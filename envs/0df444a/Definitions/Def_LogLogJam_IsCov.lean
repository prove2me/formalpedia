-- Prove2me | Definitions.Def_LogLogJam_IsCov
-- name    : LogLogJam_IsCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:21:54.535195+00:00
-- url     : https://prove2.me/theorems/918e4814-fd67-4598-94ff-af86cb764485
-- title:
--   Covariance matrices $\mathrm{Cov}_k$, $V_\theta^{\oplus k}$, and the outcome density of a Gaussian measurement
-- statement:
--   Index the $2k$ quadratures of $k$ modes in the **q-then-p** order $(q_1,\dots,q_k,p_1,\dots,p_k)$ and let $\Omega_k=\begin{pmatrix}0&I_k\\-I_k&0\end{pmatrix}$ be the standard symplectic form. A real $2k\times2k$ matrix $W$ is a **valid covariance matrix**, $W\in\mathrm{Cov}_k$, when
--
--   $$
--   W=W^\top,\qquad W+i\Omega_k\succeq0 \quad(\text{as a complex Hermitian matrix}).
--   $$
--
--   The covariance of $k$ copies $\rho_{\lambda,\theta}^{\otimes k}$ in this order is $V_{\lambda,\theta}^{\oplus k}=V_{\lambda,\theta}\otimes I_k$. A $k$-copy **Gaussian measurement** is specified by a seed $W\in\mathrm{Cov}_k$; applied to $\rho_\theta^{\otimes k}$ its outcome $y\in\mathbb R^{2k}$ has law $N\big(0,(V_\theta^{\oplus k}+W)/2\big)$, with Lebesgue density
--
--   $$
--   f^W_\theta(y)=\frac{1}{\pi^k\sqrt{\det D}}\exp\!\big(-y^\top D^{-1}y\big),\qquad D=V_\theta^{\oplus k}+W .
--   $$
--
--   These are the measurements the lower bound is about: heterodyne ($W=I$), squeezed general-dyne, and seeds entangled across the $k$ copies.
--
--   **Formalization Note** The uncertainty relation is complex positive semidefiniteness of $W+i\Omega_k$, which excludes for instance $W=0$. The density is defined for any matrix $D$; it is only evaluated at positive definite $D$.
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), §4.1, p.13 ($\Omega_n$); §4.2, pp.15–17 ($\mathrm{Cov}_n$, Gaussian measurements, q-then-p ordering); §6, p.27 (PDF p.30) (outcome density)

import Mathlib
import Definitions.Def_LogLogJam_Vsq

open Matrix
open scoped ComplexOrder

namespace LogLogJam

/-- Quadrature index set of `k` modes in the **q-then-p** ordering: `(0, j)` is the position
quadrature `q_j` and `(1, j)` the momentum quadrature `p_j` of mode `j` (arXiv:2607.12983, version
of November 3, 2026, sha256 97b751ca…, §4.2, p.14: `R̂ = (q̂₁, …, q̂_k, p̂₁, …, p̂_k)`). -/
abbrev Q (k : ℕ) : Type := Fin 2 × Fin k

/-- The standard symplectic form `Ω_k = [[0, I_k], [−I_k, 0]]` in the q-then-p ordering
(arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, §4.1, p.13). -/
def Omega (k : ℕ) : Matrix (Q k) (Q k) ℝ :=
  Matrix.kroneckerMap (· * ·) !![0, 1; -1, 0] (1 : Matrix (Fin k) (Fin k) ℝ)

/-- `W ∈ Cov_k`: `W` is a valid `k`-mode covariance matrix, i.e. a real symmetric `2k × 2k` matrix
satisfying the uncertainty relation `W + iΩ_k ⪰ 0` (arXiv:2607.12983, version of November 3, 2026,
sha256 97b751ca…, §4.2, p.15: `Cov_n := {V ∈ ℝ^{2n×2n} : V = Vᵀ, V + iΩ_n ⪰ 0}`). Seeds of
Gaussian measurements range over `Cov_k` (§4.2, p.17).

**Formalization Note** The relation is the complex Hermitian positive-semidefiniteness of
`W + iΩ_k` (q-then-p ordering), not real positive semidefiniteness of `W`: `W = 0` is excluded. -/
def IsCov (k : ℕ) (W : Matrix (Q k) (Q k) ℝ) : Prop :=
  Wᵀ = W ∧ (W.map Complex.ofReal + Complex.I • (Omega k).map Complex.ofReal).PosSemidef

/-- The covariance matrix `V_{λ,θ}^{⊕k}` of `k` copies `ρ_{λ,θ}^{⊗k}` in the q-then-p ordering,
which is `V_{λ,θ} ⊗ I_k` (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, §4.2,
p.15: "The tensored state ρ(m, V)^{⊗k} will become ρ(m ⊗ 1_k, V ⊗ I_k)"; Lemma 4.8, p.21 and the
proof of Lemma 6.1, p.28, use this block form).

**Formalization Note** Kronecker product with the `2 × 2` block outside: entry
`((a,i),(b,j)) = V_{λ,θ}(a,b) δ_{ij}`. -/
noncomputable def VsqK (lam θ : ℝ) (k : ℕ) : Matrix (Q k) (Q k) ℝ :=
  Matrix.kroneckerMap (· * ·) (Vsq lam θ) (1 : Matrix (Fin k) (Fin k) ℝ)

/-- The outcome density of a `k`-copy Gaussian measurement (arXiv:2607.12983, version of
November 3, 2026, sha256 97b751ca…, §6, p.27): with `D = V_θ^{⊕k} + W`,
`f(y) = exp(−yᵀ D⁻¹ y) / (π^k √det D)`, the density of `N(0, D/2)` on `ℝ^{2k}` with respect to
Lebesgue measure. A Gaussian measurement with seed `W ∈ Cov_k` applied to `ρ_θ^{⊗k}` has outcome
law `N(0, (V_θ^{⊕k} + W)/2)` (§4.2, p.17).

**Formalization Note** `D` is a general matrix argument; the statements only evaluate it at
`D = VsqK lam θ k + W` with `lam > 0` and `W ∈ Cov_k`, where `D` is positive definite. -/
noncomputable def outDens (k : ℕ) (D : Matrix (Q k) (Q k) ℝ) (y : Q k → ℝ) : ℝ :=
  Real.exp (-(y ⬝ᵥ (D⁻¹ *ᵥ y))) / (Real.pi ^ k * Real.sqrt D.det)

end LogLogJam



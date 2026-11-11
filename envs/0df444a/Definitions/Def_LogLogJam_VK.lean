-- Prove2me | Definitions.Def_LogLogJam_VK
-- name    : LogLogJam_VK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:22:51.211767+00:00
-- url     : https://prove2.me/theorems/93c45bea-54c7-402c-9486-e1f6217fec58
-- title:
--   Siegel disk $\mathfrak D_k$ and the covariance $V_K$ of $|\psi_K\rangle$
-- statement:
--   The **Siegel disk** is $\mathfrak D_k=\{K\in\mathbb C^{k\times k}: K=K^\top,\ KK^\dagger\prec I_k\}$. It parametrizes the $k$-mode pure zero-mean Gaussian states; the state $|\psi_K\rangle$ has covariance matrix (q-then-p order)
--
--   $$
--   V_K=\begin{pmatrix}I_k+2\,\mathrm{Re}(Q_K+R_K) & 2\,\mathrm{Im}(Q_K+R_K)\\ 2\,\mathrm{Im}(Q_K+R_K)^\top & I_k+2\,\mathrm{Re}(Q_K-R_K)\end{pmatrix},
--   $$
--
--   where $Q_K=K^\dagger K(I_k-K^\dagger K)^{-1}$ and $R_K=(I_k-KK^\dagger)^{-1}K$, with $\mathrm{Re},\mathrm{Im}$ taken entrywise. This parametrization is the tool of Lemma 6.1, where it turns $\log\det(V_\theta^{\oplus k}+W)$ into the logarithm of a holomorphic determinant.
--
--   **Formalization Note** Lemma 4.6 (a computation on Fock space) is used as the definition of $V_K$.
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), §4.4, p.18 (PDF p.21) ($\mathfrak D_k$); Lemma 4.6, p.19 (PDF p.22) ($V_K$)

import Mathlib
import Definitions.Def_LogLogJam_IsCov

open Matrix
open scoped ComplexOrder

namespace LogLogJam

/-- The Siegel disk `D_k = {K ∈ ℂ^{k×k} : K = Kᵀ, KK† ≺ I_k}` (arXiv:2607.12983, version of
November 3, 2026, sha256 97b751ca…, §4.4, p.18). -/
def InSiegelDisk {k : ℕ} (K : Matrix (Fin k) (Fin k) ℂ) : Prop :=
  Kᵀ = K ∧ (1 - K * Kᴴ).PosDef

/-- The covariance matrix `V_K` of the pure Gaussian state `|ψ_K⟩`, `K ∈ D_k`, in the q-then-p
ordering (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, Lemma 4.6, p.19):
`V_K = [[I + 2 Re(Q_K + R_K), 2 Im(Q_K + R_K)], [2 Im(Q_K + R_K)ᵀ, I + 2 Re(Q_K − R_K)]]` with
`Q_K = K†K(I − K†K)⁻¹` and `R_K = (I − KK†)⁻¹K`.

**Formalization Note** Lemma 4.6 (a computation on Fock space) is taken as the definition of
`V_K`. `Re`, `Im` are entrywise. The block index is the first coordinate of `Q k = Fin 2 × Fin k`
(`0` = position block, `1` = momentum block). -/
noncomputable def VK {k : ℕ} (K : Matrix (Fin k) (Fin k) ℂ) : Matrix (Q k) (Q k) ℝ :=
  let QK : Matrix (Fin k) (Fin k) ℂ := Kᴴ * K * (1 - Kᴴ * K)⁻¹
  let RK : Matrix (Fin k) (Fin k) ℂ := (1 - K * Kᴴ)⁻¹ * K
  Matrix.of fun a b =>
    if a.1 = 0 then
      if b.1 = 0 then (if a.2 = b.2 then 1 else 0) + 2 * ((QK + RK) a.2 b.2).re
      else 2 * ((QK + RK) a.2 b.2).im
    else
      if b.1 = 0 then 2 * ((QK + RK) b.2 a.2).im
      else (if a.2 = b.2 then 1 else 0) + 2 * ((QK - RK) a.2 b.2).re

end LogLogJam



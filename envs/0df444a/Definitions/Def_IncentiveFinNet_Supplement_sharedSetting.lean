-- Prove2me | Definitions.Def_IncentiveFinNet_Supplement_sharedSetting
-- name    : IncentiveFinNet_Supplement_sharedSetting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:31:28.157595+00:00
-- url     : https://prove2.me/theorems/ae86a5f1-932c-5207-9fb8-9bebdb1776ff
-- title:
--   The network setting $(\mu_i,\Sigma,\gamma_i)$ with shared covariance and all edges allowed, and $\Gamma^{\pm1/2}$
-- statement:
--   For an expected-return matrix $M$ (column $i$ is $\mu_i$), a covariance matrix $\Sigma\succ0$ and risk aversions $\gamma_i>0$, the network setting $(\mu_i,\Sigma,\gamma_i)_{i\in[n]}$ has
--
--   1. the **shared covariance** $\Sigma_i = \Sigma$ for every agent, and
--   2. **all edges allowed**: $J_i=[n]$, i.e. $\Psi_i = I_n$, self-investments included.
--
--   A setting written without $\Psi_i$ has all edges allowed (Definition 1). Write $\Gamma = \mathrm{diag}(\gamma_1,\dots,\gamma_n)$, $\Gamma^{1/2} = \mathrm{diag}(\sqrt{\gamma_1},\dots,\sqrt{\gamma_n})$ and $\Gamma^{-1/2} = \mathrm{diag}(1/\sqrt{\gamma_1},\dots,1/\sqrt{\gamma_n})$.
--
--   This is the setting of the closed forms of Corollary 2 and of Theorems 7 and 8.
--
--   **Formalization Note** `sharedSetting M Σ γ hγ hΣ` builds the published `IncentiveFinNet.NetworkSetting` with `Sig i = Σ` and `J i = univ`; the positivity hypotheses are arguments.
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Definition 1, p.10; Corollary 2, A.4, p.35; Theorem 8, p.25

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting

open Matrix

namespace IncentiveFinNet.Supplement

variable {n : ℕ}

/-- The network setting `(µ_i, Σ, γ_i)_{i ∈ [n]}` with a **shared covariance** `Σ_i = Σ` and **all
edges allowed** (`J_i = [n]`, i.e. `Ψ_i = I_n`, self-loops included), Jalan, Chakrabarti, Sarkar,
arXiv:2212.06808v3, Definition 1, p.10 ("When there are no constraints (i.e., all edges are
allowed), we drop the `Ψ_i = I_n` terms"); it is the setting of Corollary 2 (A.4, p.35) and of
Theorems 7 (p.19) and 8 (p.25). `M` has column `i` equal to `µ_i`.

**Formalization Note** The positivity `γ_i > 0` and `Σ ≻ 0` of Definition 1 are arguments. -/
def sharedSetting (M Sig : Matrix (Fin n) (Fin n) ℝ) (γ : Fin n → ℝ) (hγ : ∀ i, 0 < γ i)
    (hSig : Sig.PosDef) : NetworkSetting n where
  M := M
  γ := γ
  Sig := fun _ => Sig
  J := fun _ => Finset.univ
  γ_pos := hγ
  Sig_posDef := fun _ => hSig
  J_symm := by simp

/-- `Γ = diag(γ_1, …, γ_n)` (Definition 1, p.10). -/
noncomputable def Gam (γ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal γ

/-- `Γ^{1/2} = diag(√γ_1, …, √γ_n)`. -/
noncomputable def GamSqrt (γ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => Real.sqrt (γ i)

/-- `Γ^{−1/2} = diag(1/√γ_1, …, 1/√γ_n)`. -/
noncomputable def GamInvSqrt (γ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => (Real.sqrt (γ i))⁻¹

end IncentiveFinNet.Supplement



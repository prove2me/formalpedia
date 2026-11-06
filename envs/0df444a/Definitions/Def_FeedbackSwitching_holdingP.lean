-- Prove2me | Definitions.Def_FeedbackSwitching_holdingP
-- name    : FeedbackSwitching_holdingP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:28.864762+00:00
-- url     : https://prove2.me/theorems/cec78131-1e9f-4cc3-8989-88ba7d07bf53
-- title:
--   Holding family $P_\tau$ of $(p,x)$ (Definition 2, Eq. (15)) and the matrix $A=\mathrm{diag}(\lambda)-\lambda x^{\mathsf T}$
-- statement:
--   Let $p,x$ be positive probability vectors with $x\ge p/2$, and put $\lambda_s=x_s/p_s$. For a rate $0<\tau\le1$ let
--   $$
--   a^{(\tau)}_s=\frac{\tau\lambda_s}{2(1+\tau\lambda_s)},\qquad
--   P_\tau(j\mid s)=\big(1-a^{(\tau)}_s\big)\mathbf 1\{s=j\}+a^{(\tau)}_s\,\frac{p_ja^{(\tau)}_j}{\sum_rp_ra^{(\tau)}_r}.
--   $$
--   $(P_\tau)_{0<\tau\le1}$ is the **holding family** of $(p,x)$ and $x$ its **refresh law**. Also defined: $\nu_\tau(\alpha)=(2+\tau\alpha)/(2(1+\tau\alpha))$ and the matrix $A=\mathrm{diag}(\lambda)-\lambda x^{\mathsf T}$, $(Af)_s=\lambda_s(f_s-x^{\mathsf T}f)$ (Eq. (33)).
--
--   The chain $P_\tau$ keeps its state with probability $1-a_s^{(\tau)}$ and otherwise refreshes; it is reversible with respect to $p$ and switches rarely when $\tau$ is small.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Definition 2, Eq. (15), p.19 (PDF p.21); §5.3, Eq. (33), p.27 (PDF p.29)

import Mathlib
import Definitions.Def_FeedbackSwitching_centering
open Matrix

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

The hypotheses of Definition 2 (p.19 = PDF p.21): `p, x` positive probability vectors with
`x ≥ p/2`. "(p, x) is a holding family" in Lemma 7 and Corollary 2 means this. -/
def IsHoldingPair {K : ℕ} (p x : Fin K → ℝ) : Prop :=
  IsPosProbVec p ∧ IsPosProbVec x ∧ ∀ s, p s / 2 ≤ x s

/-- Relative refresh speed `λ_s = x_s / p_s` (Definition 2). -/
noncomputable def lam {K : ℕ} (p x : Fin K → ℝ) (s : Fin K) : ℝ :=
  x s / p s

/-- Refresh probability `a_s^{(τ)} = τλ_s / (2(1 + τλ_s))` (Eq. (15)). -/
noncomputable def aRate {K : ℕ} (p x : Fin K → ℝ) (τ : ℝ) (s : Fin K) : ℝ :=
  τ * lam p x s / (2 * (1 + τ * lam p x s))

/-- **Holding chain** `P_τ` of the holding family of `(p, x)` (Definition 2, Eq. (15), p.19):
`P_τ(j | s) = (1 − a_s) 1{s = j} + a_s · p_j a_j / ∑_r p_r a_r`. Entry `(s, j)` is `P_τ(j | s)`. -/
noncomputable def holdingP {K : ℕ} (p x : Fin K → ℝ) (τ : ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  Matrix.of fun s j =>
    (if s = j then 1 - aRate p x τ s else 0) +
      aRate p x τ s * (p j * aRate p x τ j / ∑ r, p r * aRate p x τ r)

/-- `ν_τ(α) = (2 + τα) / (2(1 + τα))` (§5.3, p.27). -/
noncomputable def nuRate (τ α : ℝ) : ℝ :=
  (2 + τ * α) / (2 * (1 + τ * α))

/-- The matrix `A = diag(λ) − λxᵀ`, `(Af)_s = λ_s (f_s − xᵀf)` (Eq. (33), p.27). -/
noncomputable def Amat {K : ℕ} (p x : Fin K → ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  Matrix.of fun s r => (if s = r then lam p x s else 0) - lam p x s * x r

end FeedbackSwitching



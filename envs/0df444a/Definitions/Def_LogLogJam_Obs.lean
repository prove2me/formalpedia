-- Prove2me | Definitions.Def_LogLogJam_Obs
-- name    : LogLogJam_Obs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:22:49.342547+00:00
-- url     : https://prove2.me/theorems/d06afb79-8cf2-4e87-9ec2-e50d113b0a42
-- title:
--   Observations, histories, copies consumed, likelihood, and single-step Fisher information $J_W(\theta)$
-- statement:
--   An **observation** is a triple $(k,W,y)$: a $k$-copy Gaussian measurement, identified with its seed $W$, and its outcome $y\in\mathbb R^{2k}$ ($k=0$, a null measurement, is allowed). A **history** of length $t$ is a sequence $H=(h_1,\dots,h_t)$ of observations, and it consumes $s(H)=\sum_i k_i$ copies. When the state is $\rho_{\lambda,\theta}$, the likelihood of a history is
--
--   $$
--   q_\theta(H)=\prod_{i=1}^t f^{W_i}_\theta(y_i),
--   $$
--
--   and the **single-step Fisher information** of a seed $W$ on $k$ copies is
--
--   $$
--   J_W(\theta)=\mathbb E_{Y\sim f^W_\theta}\big[(\partial_\theta\log f^W_\theta(Y))^2\big].
--   $$
--
--   These are the bookkeeping objects of Definitions 4.3 and §5.2–§6: the protocol's Fisher information is accumulated from the $J_W$ of its measurements.
--
--   **Formalization Note** The seed matrix is stored as a function $Q_k\times Q_k\to\mathbb R$ (with $Q_k=\{0,1\}\times\{1,\dots,k\}$, q-then-p) so that it carries the product $\sigma$-algebra. $J_W$ is the integral, not the closed form used inside the proof of Lemma 6.1.
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Definition 4.3, p.17 (PDF p.20); §5.2, p.23; §5.3, p.23; §6, p.27 (PDF p.30)

import Mathlib
import Definitions.Def_LogLogJam_IsCov
import Definitions.Def_LogLogJam_fisherInfo

open MeasureTheory
open scoped ENNReal

namespace LogLogJam

/-- A Gaussian-measurement seed: a number of copies `k` and a seed covariance matrix `W^{(k)}`
(arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, Definition 4.3, p.17: "In the
special case of a k-copy Gaussian measurement, we identify M with its seed covariance matrix
W^{(k)} ∈ Cov_{nk}", with `n = 1`).

**Formalization Note** The matrix is stored as a function `Q k → Q k → ℝ` (so that it carries the
product σ-algebra) and read as a matrix with `Matrix.of`. `k = 0` (a null measurement, p.18) is
allowed. -/
abbrev Seed : Type := Σ k : ℕ, (Q k → Q k → ℝ)

/-- An observation `h = (M, y)`: a `k`-copy Gaussian measurement, identified with its seed
`W ∈ Cov_k`, and its outcome `y ∈ ℝ^{2k}` (arXiv:2607.12983, version of November 3, 2026, sha256
97b751ca…, Definition 4.3, p.17). `k(M)` is the first component. -/
abbrev Obs : Type := Σ k : ℕ, (Q k → Q k → ℝ) × (Q k → ℝ)

/-- A history `H = (h₁, …, h_t)` of length `t` (arXiv:2607.12983, version of November 3, 2026,
sha256 97b751ca…, Definition 4.3, p.17). -/
abbrev Hist (t : ℕ) : Type := Fin t → Obs

/-- The number of copies `s(H) = Σ_i k(M_i)` consumed along a history (arXiv:2607.12983, version of
November 3, 2026, sha256 97b751ca…, Definition 4.3, p.17). -/
def copies {t : ℕ} (H : Hist t) : ℕ :=
  ∑ i, (H i).1

/-- The density `f^{W}_θ(y)` of one observation `(k, W, y)` when the state is `ρ_{λ,θ}`
(arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, §6, p.27). -/
noncomputable def obsDens (lam θ : ℝ) (o : Obs) : ℝ :=
  outDens o.1 (VsqK lam θ o.1 + Matrix.of o.2.1) o.2.2

/-- The likelihood `q_θ(H_t) = ∏_{i=1}^t f^{M_i}_θ(y_i)` of a history (arXiv:2607.12983, version of
November 3, 2026, sha256 97b751ca…, §5.2, p.23). -/
noncomputable def histDens {t : ℕ} (lam θ : ℝ) (H : Hist t) : ℝ :=
  ∏ i, obsDens lam θ (H i)

/-- The single-step Fisher information `J_W(θ) = E_{Y∼f^W_θ}[(∂_θ log f^W_θ(Y))²]` of a `k`-copy
Gaussian measurement with seed `W` on the squeezed family (arXiv:2607.12983, version of
November 3, 2026, sha256 97b751ca…, §5.3, p.23 and §6, p.27).

**Formalization Note** Defined as the integral (`fisherInfo` with Lebesgue measure on `ℝ^{2k}`),
not by the closed form `½ tr((D⁻¹∂_θD)²)` quoted in the proof of Lemma 6.1. -/
noncomputable def measFisher (lam : ℝ) (k : ℕ) (W : Q k → Q k → ℝ) (θ : ℝ) : ℝ≥0∞ :=
  fisherInfo volume (fun θ' y => outDens k (VsqK lam θ' k + Matrix.of W) y) θ

end LogLogJam



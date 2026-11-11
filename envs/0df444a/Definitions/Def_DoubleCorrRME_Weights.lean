-- Prove2me | Definitions.Def_DoubleCorrRME_Weights
-- name    : DoubleCorrRME_Weights
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:22.788797+00:00
-- url     : https://prove2.me/theorems/c4443a8f-d224-477a-9ef0-9d72f4ee150c
-- title:
--   Product weights, $\bar x(u,w)$, $M_s(u,w)$, the MMW density and (approximate) QUE scores
-- statement:
--   For user weights $u\in\mathbb R^N_{\ge0}$ and sample weights $w\in\mathbb R^{N\times n}_{\ge0}$, the product weights are $p_{i,j}=u_iw_{i,j}$. When $\|\mathrm{vec}(p)\|_1>0$,
--
--   $$\bar x(u,w)=\frac{\sum_{i,j}p_{i,j}x_{i,j}}{\|\mathrm{vec}(p)\|_1},\qquad M_s(u,w)=\sum_{i,j}p_{i,j}(x_{i,j}-\bar x(u,w))(x_{i,j}-\bar x(u,w))^\top .$$
--
--   For a user with $s_i(w)=\sum_jw_{i,j}>0$: $\bar x_i(w)=\frac1{s_i(w)}\sum_jw_{i,j}x_{i,j}$, $M_i(w)$ the corresponding covariance, and $\ell_i(w)=1-s_i(w)$ is the sample-weight loss.
--
--   **MMW density** (Definition 3.7): for an epoch starting at $t_0$, learning rate $\eta$ and gains $F^{(s)}$,
--
--   $$\Psi^{(t)}=\frac{\exp\big(\eta\sum_{s=t_0}^{t-1}F^{(s)}\big)}{\operatorname{tr}\exp\big(\eta\sum_{s=t_0}^{t-1}F^{(s)}\big)},\qquad \Psi^{(t_0)}=I_d/d .$$
--
--   **QUE scores** (Definition 3.8): $\tau_{i,j}=(x_{i,j}-\bar x(u,w))^\top\Psi(x_{i,j}-\bar x(u,w))$. A nonnegative $\tilde\tau$ is a **$\nu$-approximate** QUE score matrix (Definition 3.9) if $(1-\nu)\tau_{i,j}\le\tilde\tau_{i,j}\le(1+\nu)\tau_{i,j}$ for every $i$ with $u_i>0$ and every $j$.
--
--   **Formalization Note** Lean returns $0$ for $\bar x$ when $p=0$; every statement assumes or proves $\|\mathrm{vec}(p)\|_1>0$. The matrix exponential is Mathlib's power series.
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), §3 notation, p.15 (PDF p.16); Definitions 3.7–3.9, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_DoubleCorrRME_Model

namespace DoubleCorrRME

/-!
# Product weights, weighted statistics, the MMW density and QUE scores

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…): §3 notation, p.15
(PDF p.16); Definitions 3.7, 3.8, 3.9, p.18 (PDF p.19).

**Formalization Note.**
* User weights are `u : Fin N → ℝ`, sample weights `w : Fin N → Fin n → ℝ`, and the product-weight
  matrix is `p := diag(u) w`, `p_{i,j} = u_i w_{i,j}`. `‖vec(p)‖₁ = ∑_{i,j} |p_{i,j}|`.
* `x̄(u, w)` divides by `‖vec(p)‖₁`; the paper defines it only when `‖vec(p)‖₁ > 0`, and on `p = 0`
  Lean returns `0`. Every statement that uses it either assumes or proves `‖vec(p)‖₁ > 0`.
  `M_s(u, w)` is unnormalized, as printed. `x̄_i(w)`, `M_i(w)` divide by `s_i(w)`, likewise defined
  only when `s_i(w) > 0`.
* The matrix exponential is Mathlib's `NormedSpace.exp` on `Matrix (Fin d) (Fin d) ℝ` (a convergent
  power series, independent of the choice of matrix norm). For `d ≥ 1` the trace of the exponential
  of a symmetric matrix is positive, so the MMW normalization never divides by `0`.
* The epoch start `t₀`, the learning rate `η` and the gains `F` are arguments of the MMW density; the
  gains used are `F^(s)` for `t₀ ≤ s < t`, so `Ψ^(t₀) = I_d/d`.
* `⟨A, B⟩` is the Frobenius inner product, `⟨p, τ⟩ = ∑_{i,j} p_{i,j} τ_{i,j}`.
-/

/-- The product-weight matrix `p := diag(u) w`. -/
def prodW {N n : ℕ} (u : Fin N → ℝ) (w : Fin N → Fin n → ℝ) : Fin N → Fin n → ℝ :=
  fun i j => u i * w i j

/-- `‖vec(p)‖₁ = ∑_{i,j} |p_{i,j}|`. -/
def l1P {N n : ℕ} (p : Fin N → Fin n → ℝ) : ℝ := ∑ i, ∑ j, |p i j|

/-- `‖u‖₁ = ∑_i |u_i|`. -/
def l1U {N : ℕ} (u : Fin N → ℝ) : ℝ := ∑ i, |u i|

/-- `⟨p, τ⟩ = ∑_{i,j} p_{i,j} τ_{i,j}`. -/
def pairing {N n : ℕ} (p τ : Fin N → Fin n → ℝ) : ℝ := ∑ i, ∑ j, p i j * τ i j

/-- The weighted sample mean `x̄(u, w) := ∑_{i,j} p_{i,j} x_{i,j} / ‖vec(p)‖₁`. -/
noncomputable def wMean {N n d : ℕ} (x : Fin N → Fin n → Vec d) (u : Fin N → ℝ)
    (w : Fin N → Fin n → ℝ) : Vec d :=
  (l1P (prodW u w))⁻¹ • ∑ i, ∑ j, prodW u w i j • x i j

/-- The unnormalized weighted sample covariance
`M_s(u, w) := ∑_{i,j} p_{i,j} (x_{i,j} − x̄(u, w))(x_{i,j} − x̄(u, w))⊤`. -/
noncomputable def covS {N n d : ℕ} (x : Fin N → Fin n → Vec d) (u : Fin N → ℝ)
    (w : Fin N → Fin n → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ i, ∑ j, prodW u w i j • outer (x i j - wMean x u w)

/-- `s_i(w) := ∑_j w_{i,j}`. -/
def userSum {N n : ℕ} (w : Fin N → Fin n → ℝ) (i : Fin N) : ℝ := ∑ j, w i j

/-- `x̄_i(w) := (1/s_i(w)) ∑_j w_{i,j} x_{i,j}` (the `y_i` of Lemma 5.16). -/
noncomputable def userMean {N n d : ℕ} (x : Fin N → Fin n → Vec d) (w : Fin N → Fin n → ℝ)
    (i : Fin N) : Vec d :=
  (userSum w i)⁻¹ • ∑ j, w i j • x i j

/-- `M_i(w) := (1/s_i(w)) ∑_j w_{i,j} (x_{i,j} − x̄_i(w))(x_{i,j} − x̄_i(w))⊤`. -/
noncomputable def userCov {N n d : ℕ} (x : Fin N → Fin n → Vec d) (w : Fin N → Fin n → ℝ)
    (i : Fin N) : Matrix (Fin d) (Fin d) ℝ :=
  (userSum w i)⁻¹ • ∑ j, w i j • outer (x i j - userMean x w i)

/-- The sample-weight loss `ℓ_i(w) := 1 − s_i(w)`. -/
def loss {N n : ℕ} (w : Fin N → Fin n → ℝ) (i : Fin N) : ℝ := 1 - userSum w i

/-- `Ψ ∈ 𝒟_d`: a density matrix, `Ψ ⪰ 0` and `tr Ψ = 1` (Definition 3.7). -/
def IsDensity {d : ℕ} (Ψ : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  Ψ.PosSemidef ∧ Ψ.trace = 1

/-- Definition 3.7. The MMW density matrix of the epoch starting at `t₀`, with learning rate `η`
and gains `F`: `Ψ^(t) := exp(η ∑_{s=t₀}^{t−1} F^(s)) / tr[exp(η ∑_{s=t₀}^{t−1} F^(s))]`. -/
noncomputable def mmwDensity {d : ℕ} (η : ℝ) (F : ℕ → Matrix (Fin d) (Fin d) ℝ) (t₀ t : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.trace (NormedSpace.exp (η • ∑ s ∈ Finset.Ico t₀ t, F s)))⁻¹ •
    NormedSpace.exp (η • ∑ s ∈ Finset.Ico t₀ t, F s)

/-- Definition 3.8. The QUE score matrix
`τ_{i,j} := (x_{i,j} − x̄(u, w))⊤ Ψ (x_{i,j} − x̄(u, w))`. -/
noncomputable def queScore {N n d : ℕ} (x : Fin N → Fin n → Vec d) (u : Fin N → ℝ)
    (w : Fin N → Fin n → ℝ) (Ψ : Matrix (Fin d) (Fin d) ℝ) : Fin N → Fin n → ℝ :=
  fun i j => quad Ψ (x i j - wMean x u w)

/-- Definition 3.9. `τ̃ ∈ ℝ^{N×n}_{≥0}` is a `ν`-approximate QUE score matrix:
`(1 − ν) τ_{i,j} ≤ τ̃_{i,j} ≤ (1 + ν) τ_{i,j}` for every `i` with `u_i > 0` and every `j`. -/
def IsApproxQUE {N n d : ℕ} (ν : ℝ) (x : Fin N → Fin n → Vec d) (u : Fin N → ℝ)
    (w : Fin N → Fin n → ℝ) (Ψ : Matrix (Fin d) (Fin d) ℝ) (τ' : Fin N → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ τ' i j) ∧
    ∀ i, 0 < u i → ∀ j, (1 - ν) * queScore x u w Ψ i j ≤ τ' i j ∧
      τ' i j ≤ (1 + ν) * queScore x u w Ψ i j

end DoubleCorrRME



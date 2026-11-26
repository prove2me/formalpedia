-- Prove2me | Definitions.Def_Arxiv2401_10389_Basic
-- name    : Arxiv2401_10389_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-26T13:13:19.48924+00:00
-- url     : https://prove2.me/theorems/e44cf297-d561-5cbc-969e-8daa6f028cdb
-- title:
--   Forward model, linear operator and Tikhonov estimate for ultrasound phase-aberration correction
-- statement:
--   Objects of Section II and Supplemental materials C of Xing, Malescot, Martineau, Rungta and Provost (2025), all at the central angular frequency $\omega_0$.
--
--   1. **Probe and medium.** A one-dimensional probe has $N_e$ elements and the medium consists of $N_s$ point scatterers. The transmission operator $T$ and the reflection operator $R$ are complex $N_e\times N_s$ matrices, and the backscattering matrix is the diagonal matrix $\Gamma=\operatorname{diag}(\gamma)$, $\gamma\in\mathbb{C}^{N_s}$.
--   2. **Model signals (eqs. 2 and 5).** Without aberration, element $m$ receives $\hat M_m(\Gamma)=\sum_{s}\sum_{n}R_{m,s}\Gamma_{s,s}T_{n,s}$. With per-element aberration factors $u\in\mathbb{C}^{N_e}$ acting identically on transmit and receive, it receives $\hat M_m(\Gamma,u)=\sum_s\sum_n u_mR_{m,s}\Gamma_{s,s}T_{n,s}u_n$.
--   3. **Matrix form (eqs. 6, 7, 10).** The transfer matrix is $H=R\,\Gamma\,T^T$ (plain transpose). The forward model is $\hat M(\Gamma,u)=u\circ Hu$, with $\circ$ the entrywise product. Its gradient matrix is $\nabla_u\hat M(\Gamma,u)=\operatorname{diag}(Hu)+\operatorname{diag}(u)H$.
--   4. **Linear operator (eq. 13).** The augmented unknown is $(u\,|\,1)^T\in\mathbb{C}^{N_e+1}$. The $N_e\times(N_e+1)$ operator is $K(\Gamma,u_0)=\big(\nabla_u\hat M(\Gamma,u_0)\ \big|\ \hat M(\Gamma,u_0)-\nabla_u\hat M(\Gamma,u_0)u_0\big)$.
--   5. **Regularization (eqs. 14, 15, 35).** $\|v\|^2=\sum_i|v_i|^2$. For a forward operator $K$, a real matrix $L$, a parameter $\alpha$ and a signal $s$, the Tikhonov objective is $\|s-Kv\|^2+\alpha\|Lv\|^2$. The normal matrix is $K^\dagger K+\alpha L^TL$, with $K^\dagger$ the conjugate transpose, and the closed-form estimate is $(K^\dagger K+\alpha L^TL)^{-1}K^\dagger s$. $D_2$ is the $n\times n$ second-difference matrix with first row $(-1,1,0,\dots)$, interior rows $(\dots,1,-2,1,\dots)$ centred on the diagonal, and last row $(\dots,0,-1,1)$.
--   6. **Multiple transmit angles (eqs. 16-18).** For $N_\theta$ angles with per-element transmit delays $\tau_n(\theta)$, $(T_\theta)_{n,s}=T_{n,s}e^{i\omega_0\tau_n(\theta)}$. The vectorized multi-angle signal has entry $(\theta,m)$ equal to $\hat M(\Gamma,u)_m$ computed with $T_\theta$, the aberration $u$ being the same for all angles. $K_\theta(\Gamma,u_0)$ stacks the operators $K(\Gamma,u_0)$ built with $T_1,\dots,T_{N_\theta}$.
--
--   **Formalization Note** Rows of the stacked operator are indexed by pairs $(\theta,m)$ rather than by a single integer; the order of the stacking does not affect any statement. $D_2$ is written for every $n$, and the printed pattern is consistent for $n\ge2$. The statements use $n=N_e+1$, the length of the augmented unknown, with $N_e\ge1$.
-- source:
--   Xing, Malescot, Martineau, Rungta and Provost, Inverse Problem Approach to Aberration Correction for in vivo Transcranial Imaging Based on a Sparse Representation of Contrast-enhanced Ultrasound Data, arXiv:2401.10389v3 (2025), Sections II.A-II.D (eqs. (2), (5)-(7), (10), (13)-(18)), Supplemental materials C (eq. (35)), PDF pp. 2-4, 17

import Mathlib

/-!
Xing, Malescot, Martineau, Rungta and Provost, *Inverse Problem Approach to Aberration Correction
for in vivo Transcranial Imaging Based on a Sparse Representation of Contrast-enhanced Ultrasound
Data*, arXiv:2401.10389v3 (2025): the single-frequency forward model of a probe with `Ne` elements
insonifying `Ns` point scatterers through a phase-screen aberrator (Sections II.A and II.B), its
gradient and first-order linearization (Section II.B), the Tikhonov-regularized least-squares
solution with the second-difference matrix (Section II.C and Supplemental materials C), and the
multi-angle operator (Section II.D). All operators are taken at the central frequency `ω₀`.
-/

open Matrix

noncomputable section

namespace Arxiv2401_10389

variable {Ne Ns : ℕ}

/-- Eq. (2), Section II.A, PDF p. 2: the model signal on receive element `m` without aberration,
`M̂_m(Γ) = ∑_s ∑_n R_{m,s} Γ_{s,s} T_{n,s}`. The reflection operator `R` and the transmission
operator `T` are `Ne × Ns` complex matrices, and the diagonal backscattering matrix is
`Γ = diag γ`. -/
def unaberratedSignal (R : Matrix (Fin Ne) (Fin Ns) ℂ) (γ : Fin Ns → ℂ)
    (T : Matrix (Fin Ne) (Fin Ns) ℂ) : Fin Ne → ℂ :=
  fun m => ∑ s, ∑ n, R m s * γ s * T n s

/-- Eq. (5), Section II.A, PDF p. 3: the model signal on receive element `m` with the same
aberration factors `u_n` on transmit and receive,
`M̂_m(Γ, u) = ∑_s ∑_n u_m R_{m,s} Γ_{s,s} T_{n,s} u_n`. -/
def aberratedSignal (R : Matrix (Fin Ne) (Fin Ns) ℂ) (γ : Fin Ns → ℂ)
    (T : Matrix (Fin Ne) (Fin Ns) ℂ) (u : Fin Ne → ℂ) : Fin Ne → ℂ :=
  fun m => ∑ s, ∑ n, u m * R m s * γ s * T n s * u n

/-- Eq. (7), Section II.B, PDF p. 3: the transfer matrix `H = R Γ Tᵀ` (plain transpose), an
`Ne × Ne` matrix that does not depend on the aberration. -/
def transferMatrix (R : Matrix (Fin Ne) (Fin Ns) ℂ) (γ : Fin Ns → ℂ)
    (T : Matrix (Fin Ne) (Fin Ns) ℂ) : Matrix (Fin Ne) (Fin Ne) ℂ :=
  R * diagonal γ * Tᵀ

/-- Eq. (6), Section II.B, PDF p. 3: the forward model in matrix form, `M̂(Γ, u) = u ∘ H u`,
with `∘` the Hadamard (entrywise) product. -/
def forwardModel (R : Matrix (Fin Ne) (Fin Ns) ℂ) (γ : Fin Ns → ℂ)
    (T : Matrix (Fin Ne) (Fin Ns) ℂ) (u : Fin Ne → ℂ) : Fin Ne → ℂ :=
  fun m => u m * (transferMatrix R γ T *ᵥ u) m

/-- Eq. (10), Section II.B, PDF p. 3: the gradient matrix
`∇_u M̂(Γ, u) = diag(H u) + diag(u) H`. -/
def forwardGradient (R : Matrix (Fin Ne) (Fin Ns) ℂ) (γ : Fin Ns → ℂ)
    (T : Matrix (Fin Ne) (Fin Ns) ℂ) (u : Fin Ne → ℂ) : Matrix (Fin Ne) (Fin Ne) ℂ :=
  diagonal (transferMatrix R γ T *ᵥ u) + diagonal u * transferMatrix R γ T

/-- Eq. (13b), Section II.B, PDF p. 4: the augmented unknown `(u | 1)ᵀ` of length `Ne + 1`,
whose last entry is `1`. -/
def augment (u : Fin Ne → ℂ) : Fin (Ne + 1) → ℂ :=
  fun j => if h : (j : ℕ) < Ne then u ⟨j, h⟩ else 1

/-- Eq. (13a), Section II.B, PDF p. 4: the `Ne × (Ne + 1)` forward operator
`K(Γ, u₀) = (∇_u M̂(Γ, u₀) | M̂(Γ, u₀) - ∇_u M̂(Γ, u₀) u₀)`: the first `Ne` columns are the
gradient at `u₀`, the last column is `M̂(Γ, u₀) - ∇_u M̂(Γ, u₀) u₀`. -/
def linearOperator (R : Matrix (Fin Ne) (Fin Ns) ℂ) (γ : Fin Ns → ℂ)
    (T : Matrix (Fin Ne) (Fin Ns) ℂ) (u₀ : Fin Ne → ℂ) : Matrix (Fin Ne) (Fin (Ne + 1)) ℂ :=
  fun m j => if h : (j : ℕ) < Ne then forwardGradient R γ T u₀ m ⟨j, h⟩
    else forwardModel R γ T u₀ m - (forwardGradient R γ T u₀ *ᵥ u₀) m

/-- Supplemental materials C, eq. (35), PDF p. 17: the `n × n` second-difference matrix `D₂`,
with first row `(-1, 1, 0, …)`, interior rows `(…, 1, -2, 1, …)` centred on the diagonal, and
last row `(…, 0, -1, 1)`. (The printed pattern is consistent for `n ≥ 2`; statements use
`n = Ne + 1` with `Ne ≥ 1`.) -/
def secondDiffMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if (i : ℕ) = 0 then
      (if (j : ℕ) = 0 then -1 else if (j : ℕ) = 1 then 1 else 0)
    else if (i : ℕ) + 1 = n then
      (if (j : ℕ) + 2 = n then -1 else if (j : ℕ) + 1 = n then 1 else 0)
    else
      (if (j : ℕ) + 1 = (i : ℕ) then 1 else if (j : ℕ) = (i : ℕ) then -2
        else if (j : ℕ) = (i : ℕ) + 1 then 1 else 0)

/-- The squared Euclidean norm `‖v‖² = ∑_i |v_i|²` of a complex vector, used in eq. (14). -/
def sqNorm {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq (v i)

/-- Eq. (14), Section II.C, PDF p. 4: the Tikhonov-regularized least-squares objective
`‖s - K v‖² + α ‖L v‖²` for a forward operator `K`, a real regularization matrix `L`, a
regularization parameter `α` and a measured signal `s`. -/
def tikhonovObjective {ι : Type*} [Fintype ι] {p : ℕ} (K : Matrix ι (Fin p) ℂ)
    (L : Matrix (Fin p) (Fin p) ℝ) (α : ℝ) (s : ι → ℂ) (v : Fin p → ℂ) : ℝ :=
  sqNorm (s - K *ᵥ v) + α * sqNorm (L.map (fun x : ℝ => (x : ℂ)) *ᵥ v)

/-- Eq. (15), Section II.C, PDF p. 4: the normal matrix `K† K + α Lᵀ L`, with `K†` the
conjugate transpose. -/
def normalMatrix {ι : Type*} [Fintype ι] {p : ℕ} (K : Matrix ι (Fin p) ℂ)
    (L : Matrix (Fin p) (Fin p) ℝ) (α : ℝ) : Matrix (Fin p) (Fin p) ℂ :=
  Kᴴ * K + (α : ℂ) • ((L.map (fun x : ℝ => (x : ℂ)))ᵀ * L.map (fun x : ℝ => (x : ℂ)))

/-- Eq. (15), Section II.C, PDF p. 4: the closed-form estimate
`û = (K† K + α Lᵀ L)⁻¹ K† s`. -/
def tikhonovSolution {ι : Type*} [Fintype ι] {p : ℕ} (K : Matrix ι (Fin p) ℂ)
    (L : Matrix (Fin p) (Fin p) ℝ) (α : ℝ) (s : ι → ℂ) : Fin p → ℂ :=
  (normalMatrix K L α)⁻¹ *ᵥ (Kᴴ *ᵥ s)

variable {Nθ : ℕ}

/-- Eq. (16), Section II.D, PDF p. 4: the transmission operator for transmit angle `θ`,
`T_θ = T ∘ A(θ)`, with per-element transmit phase `A_n(ω₀, θ) = exp(i ω₀ τ_n(θ))`. -/
def angleTransmit (T : Matrix (Fin Ne) (Fin Ns) ℂ) (ω₀ : ℝ) (τ : Fin Nθ → Fin Ne → ℝ)
    (θ : Fin Nθ) : Matrix (Fin Ne) (Fin Ns) ℂ :=
  fun n s => T n s * Complex.exp (Complex.I * (ω₀ : ℂ) * (τ θ n : ℂ))

/-- Section II.D, PDF p. 4: the vectorized multi-angle model signal; its entry `(θ, m)` is the
forward model (6) for transmit operator `T_θ` and the angle-independent aberration `u`. -/
def multiAngleSignal (R : Matrix (Fin Ne) (Fin Ns) ℂ) (γ : Fin Ns → ℂ)
    (T : Matrix (Fin Ne) (Fin Ns) ℂ) (ω₀ : ℝ) (τ : Fin Nθ → Fin Ne → ℝ) (u : Fin Ne → ℂ) :
    Fin Nθ × Fin Ne → ℂ :=
  fun x => forwardModel R γ (angleTransmit T ω₀ τ x.1) u x.2

/-- Eq. (18), Section II.D, PDF p. 4: the stacked operator `K_θ(Γ, u₀)`, whose block for angle
`θ` is the operator (13a) built with `T_θ`. Rows are indexed by pairs `(θ, m)`. -/
def multiAngleOperator (R : Matrix (Fin Ne) (Fin Ns) ℂ) (γ : Fin Ns → ℂ)
    (T : Matrix (Fin Ne) (Fin Ns) ℂ) (ω₀ : ℝ) (τ : Fin Nθ → Fin Ne → ℝ) (u₀ : Fin Ne → ℂ) :
    Matrix (Fin Nθ × Fin Ne) (Fin (Ne + 1)) ℂ :=
  fun x j => linearOperator R γ (angleTransmit T ω₀ τ x.1) u₀ x.2 j

end Arxiv2401_10389



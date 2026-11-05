-- Prove2me | Definitions.Def_MultiParamQEC_Estimation
-- name    : MultiParamQEC_Estimation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:37:16.500389+00:00
-- url     : https://prove2.me/theorems/4911fcaf-de92-4c0c-81fc-8aabceb8525a
-- title:
--   Multi-parameter estimation on pure states: cost $\mathrm{Tr}(W\Sigma)$, local unbiasedness, the Matsumoto program (11) and the frame program (19)
-- statement:
--   Let $\mathcal H=\mathbb C^n$ be a finite-dimensional Hilbert space with inner product $\langle x|y\rangle$ (conjugate-linear in $x$), and let $\omega\mapsto|\psi_\omega\rangle$, $\omega\in\mathbb R^P$, be a family of pure states. A measurement is a POVM $\{M_\ell\}_{\ell\in\mathbb N}$ (positive semidefinite $M_\ell$ with $\sum_\ell M_\ell=\mathbb 1$), and an estimator is a map $\tilde{\boldsymbol\omega}:\mathbb N\to\mathbb R^P$.
--
--   1. The **outcome probabilities** are $p_\ell(\omega)=\langle\psi_\omega|M_\ell|\psi_\omega\rangle=\mathrm{Tr}(\rho_\omega M_\ell)$.
--   2. The estimator is **locally unbiased** at $\omega_0$ when
--   $$\sum_\ell\tilde\omega_j(\ell)\,p_\ell(\omega_0)=\omega_{0,j},\qquad \sum_\ell\tilde\omega_j(\ell)\,\partial_ip_\ell(\omega_0)=\delta_{ij},$$
--   and every variance $\sum_\ell p_\ell(\omega_0)(\tilde\omega_j(\ell)-\omega_{0,j})^2$ converges.
--   3. Its **covariance matrix** is $\Sigma_{ij}=\sum_\ell p_\ell(\omega_0)(\tilde\omega_i(\ell)-\omega_{0,i})(\tilde\omega_j(\ell)-\omega_{0,j})$, and for a real cost matrix $W$ its **cost** is $\Delta^2_W\tilde{\boldsymbol\omega}=\mathrm{Tr}(W\Sigma)$.
--   4. The **cost set** of the family at $\omega_0$ is the set of costs of all POVMs and all locally unbiased estimators at $\omega_0$.
--   5. Given $|\psi\rangle$ and vectors $\partial_j|\psi\rangle$, vectors $|x_1\rangle,\dots,|x_P\rangle\in\mathrm{span}\{|\psi\rangle,\partial_1|\psi\rangle,\dots,\partial_P|\psi\rangle\}\oplus\mathbb C^P$ are **Matsumoto-feasible** when $2\,\mathrm{Re}\langle x_i|\partial_j\psi\rangle=\delta_{ij}$, $\langle x_i|\psi\rangle=0$ and $\mathrm{Im}\langle x_i|x_j\rangle=0$; the **Matsumoto set** is the set of values $\mathrm{Tr}(WV)$, $V_{ij}=\langle x_i|x_j\rangle$, over feasible families.
--   6. The **frame set** is the set of values $\mathrm{Tr}(W(D^TD)^{-1})$, $D_{ij}=2\,\mathrm{Re}\langle c_i|\partial_j\psi\rangle$, over orthonormal $|c_1\rangle,\dots,|c_P\rangle\in\mathcal H$ orthogonal to $|\psi\rangle$ with $D$ invertible.
--
--   These are the objects of the Matsumoto bound (11) and its reformulation (19), on which the optimization of error-corrected protocols is built.
--
--   **Formalization Note** The derivative $\partial_ip_\ell(\omega_0)$ is the genuine Fréchet derivative of $\omega\mapsto p_\ell(\omega)$ in the $i$-th coordinate direction. Sums over outcomes are unconditional (`HasSum`), so convergence is part of local unbiasedness. The direct sum $\mathcal H\oplus\mathbb C^P$ is $\mathbb C^{n\sqcup P}$. In the frame set the constraint $\langle c_i|\psi\rangle=0$ comes from the text (the $c_i$ span the $x_i$); the printed display (19) omits it. $D$ is required invertible so that $(D^TD)^{-1}$ is a genuine inverse.
-- source:
--   Górecki–Zhou–Jiang–Demkowicz-Dobrzański, Optimal probes and error-correction schemes in multi-parameter quantum metrology, arXiv:1901.00896v4, Sec. 2, p.3, Eqs. (2)–(4); Sec. 4.1, p.6, Eq. (11); Sec. 4.2.1, p.7, Eqs. (18)–(19)

import Mathlib
import Definitions.Def_ObliviousRSP_IsPOVM

open scoped ComplexOrder Matrix

namespace MultiParamQEC

/-!
# Multi-parameter estimation on a pure-state family: cost, local unbiasedness, Matsumoto bound

Górecki–Zhou–Jiang–Demkowicz-Dobrzański, *Optimal probes and error-correction schemes in
multi-parameter quantum metrology*, arXiv:1901.00896v4, Sec. 2, p.3, Eqs. (2)–(4) (covariance,
cost `Δ²_W ω̃ = Tr(WΣ)`, local unbiasedness), and Sec. 4.1–4.2.1, pp.6–7, Eqs. (11) and (19)
(the Matsumoto bound and its orthonormal-frame form).

The state space is `ℂ^n` for a finite type `n`, with inner product `⟨x|y⟩ = star x ⬝ᵥ y`
(conjugate-linear in the first slot). A family of pure states is a map
`ψ : (Fin P → ℝ) → n → ℂ`, `ω ↦ |ψ_ω⟩`; a measurement is a POVM `M : ℕ → Matrix n n ℂ`
(`ObliviousRSP.IsPOVM`, positive semidefinite elements with `HasSum M 1`), so a finite POVM is
the special case with `M ℓ = 0` for all large `ℓ`; an estimator is `ω̃ : ℕ → Fin P → ℝ`.

**Formalization Note.** The outcome probability is `p_ℓ(ω) = Re⟨ψ_ω|M_ℓ|ψ_ω⟩ = Tr(ρ_ω M_ℓ)`.
The derivative `∂_i p_ℓ(ω₀)` in the local-unbiasedness condition (4) is the genuine Fréchet
derivative of `ω ↦ p_ℓ(ω)` at `ω₀` in the direction of the `i`-th coordinate vector. The sums of
(2) and (4) over countably many outcomes are `HasSum` (unconditional, so convergence is part of
the condition), and the variances `Σ_ℓ p_ℓ (ω̃_i(ℓ) − ω_{0,i})²` are required to be summable; the
covariance entries are then absolutely convergent `tsum`s.
-/

variable {n : Type} [Fintype n] [DecidableEq n] {P : ℕ}

/-- Outcome probability `p_ℓ = Re⟨ψ|M_ℓ|ψ⟩ = Tr(|ψ⟩⟨ψ| M_ℓ)` of outcome `ℓ` of the measurement `M`
on the pure state `ψ` (arXiv:1901.00896v4, Eq. (2), p.3). -/
noncomputable def outcomeProb (M : ℕ → Matrix n n ℂ) (ψ : n → ℂ) (ℓ : ℕ) : ℝ :=
  (star ψ ⬝ᵥ (M ℓ *ᵥ ψ)).re

/-- Local unbiasedness at the point `ω₀` (arXiv:1901.00896v4, Eq. (4), p.3): given the outcome
probabilities `p ℓ = p_ℓ(ω₀)` and their partial derivatives `dp ℓ i = ∂_i p_ℓ(ω₀)`, the estimator
`est` satisfies `Σ_ℓ ω̃_j(ℓ) p_ℓ = ω_{0,j}` and `Σ_ℓ ω̃_j(ℓ) ∂_i p_ℓ = δ_ij`; moreover every
variance `Σ_ℓ p_ℓ (ω̃_j(ℓ) − ω_{0,j})²` converges, so that the covariance (2) is defined. -/
def IsLocallyUnbiased (p : ℕ → ℝ) (dp : ℕ → Fin P → ℝ) (ω₀ : Fin P → ℝ)
    (est : ℕ → Fin P → ℝ) : Prop :=
  (∀ j, HasSum (fun ℓ => est ℓ j * p ℓ) (ω₀ j)) ∧
  (∀ i j, HasSum (fun ℓ => est ℓ j * dp ℓ i) (if i = j then 1 else 0)) ∧
  (∀ j, Summable (fun ℓ => p ℓ * (est ℓ j - ω₀ j) ^ 2))

/-- Estimator covariance matrix `Σ_ij = Σ_ℓ p_ℓ (ω̃_i(ℓ) − ω_{0,i})(ω̃_j(ℓ) − ω_{0,j})`
(arXiv:1901.00896v4, Eq. (2), p.3). -/
noncomputable def covariance (p : ℕ → ℝ) (ω₀ : Fin P → ℝ) (est : ℕ → Fin P → ℝ) :
    Matrix (Fin P) (Fin P) ℝ :=
  Matrix.of fun i j => ∑' ℓ, p ℓ * (est ℓ i - ω₀ i) * (est ℓ j - ω₀ j)

/-- The scalar cost `Δ²_W ω̃ = Tr(WΣ)` (arXiv:1901.00896v4, Eq. (3), p.3). -/
noncomputable def estCost (W : Matrix (Fin P) (Fin P) ℝ) (p : ℕ → ℝ) (ω₀ : Fin P → ℝ)
    (est : ℕ → Fin P → ℝ) : ℝ :=
  (W * covariance p ω₀ est).trace

/-- `∂_j|ψ_ω⟩` at `ω₀`: the Fréchet derivative of the family in the `j`-th coordinate direction. -/
noncomputable def partialDeriv (ψ : (Fin P → ℝ) → n → ℂ) (ω₀ : Fin P → ℝ) (j : Fin P) : n → ℂ :=
  fderiv ℝ ψ ω₀ (Pi.single j 1)

/-- The set of all costs `Tr(WΣ)` achievable at the point `ω₀` on the pure-state family `ψ` by a
POVM with countably many outcomes and a locally unbiased estimator (arXiv:1901.00896v4,
Eqs. (2)–(4), p.3). The derivative `∂_i p_ℓ(ω₀)` is the genuine derivative of
`ω ↦ Re⟨ψ_ω|M_ℓ|ψ_ω⟩`. -/
def familyCostSet (ψ : (Fin P → ℝ) → n → ℂ) (ω₀ : Fin P → ℝ) (W : Matrix (Fin P) (Fin P) ℝ) :
    Set ℝ :=
  {c | ∃ (M : ℕ → Matrix n n ℂ) (est : ℕ → Fin P → ℝ), ObliviousRSP.IsPOVM M ∧
      IsLocallyUnbiased (fun ℓ => outcomeProb M (ψ ω₀) ℓ)
        (fun ℓ i => fderiv ℝ (fun ω => outcomeProb M (ψ ω) ℓ) ω₀ (Pi.single i 1)) ω₀ est ∧
      c = estCost W (fun ℓ => outcomeProb M (ψ ω₀) ℓ) ω₀ est}

/-- The vectors `|x_1⟩, …, |x_P⟩ ∈ span{|ψ⟩, ∂_1|ψ⟩, …, ∂_P|ψ⟩} ⊕ ℂ^P` are feasible for the
Matsumoto bound (arXiv:1901.00896v4, Eq. (11), p.6): `2Re⟨x_i|∂_jψ⟩ = δ_ij`, `⟨x_i|ψ⟩ = 0` and
`Im⟨x_i|x_j⟩ = 0`. The direct sum is `ℂ^(n ⊕ Fin P)`; `ψ` and `∂_jψ` sit in the first summand
(`Sum.elim · 0`), and the first-summand component of each `x_i` lies in the complex span of
`ψ, v_1, …, v_P`, where `v j` stands for `∂_j|ψ⟩`. -/
def IsMatsumotoFeasible (ψ : n → ℂ) (v : Fin P → n → ℂ) (x : Fin P → (n ⊕ Fin P) → ℂ) : Prop :=
  (∀ i, (fun k => x i (Sum.inl k)) ∈ Submodule.span ℂ (insert ψ (Set.range v))) ∧
  (∀ i j, 2 * (star (x i) ⬝ᵥ Sum.elim (v j) 0).re = if i = j then 1 else 0) ∧
  (∀ i, star (x i) ⬝ᵥ Sum.elim ψ 0 = 0) ∧
  (∀ i j, (star (x i) ⬝ᵥ x j).im = 0)

/-- The real Gram matrix `V_ij = Re⟨x_i|x_j⟩` (equal to `⟨x_i|x_j⟩` under `Im V = 0`). -/
noncomputable def gramRe {ι : Type} [Fintype ι] (x : Fin P → ι → ℂ) : Matrix (Fin P) (Fin P) ℝ :=
  Matrix.of fun i j => (star (x i) ⬝ᵥ x j).re

/-- The values `Tr(WV)` of the Matsumoto program (arXiv:1901.00896v4, Eq. (11), p.6) over all
feasible `|x_i⟩`; `v j` stands for `∂_j|ψ_ω⟩`. -/
def matsumotoSet (ψ : n → ℂ) (v : Fin P → n → ℂ) (W : Matrix (Fin P) (Fin P) ℝ) : Set ℝ :=
  {t | ∃ x : Fin P → (n ⊕ Fin P) → ℂ, IsMatsumotoFeasible ψ v x ∧ t = (W * gramRe x).trace}

/-- The matrix `D_ij = 2Re⟨c_i|∂_jψ⟩` of a frame `c_1, …, c_P` (arXiv:1901.00896v4, Eq. (18)–(19),
p.7); rows are indexed by the frame, columns by the parameters. -/
noncomputable def frameMatrix (v : Fin P → n → ℂ) (c : Fin P → n → ℂ) : Matrix (Fin P) (Fin P) ℝ :=
  Matrix.of fun i j => 2 * (star (c i) ⬝ᵥ v j).re

/-- The values `Tr(W(DᵀD)⁻¹)` of the orthonormal-frame program (arXiv:1901.00896v4, Eq. (19),
p.7) over orthonormal `c_1, …, c_P ∈ H` orthogonal to `|ψ⟩`, with `D` invertible.

**Formalization Note.** The frame is required to be orthogonal to `|ψ⟩`: in the text the `c_i`
are an orthonormal basis of `span{x_1, …, x_P}` and every `x_i ⊥ ψ` by (14); the printed display
(19) omits this constraint and is false without it (see the milestone `eq_19`). `D` is required
invertible so that `(DᵀD)⁻¹` is the genuine inverse and not Mathlib's junk value `0`. -/
noncomputable def frameSet (ψ : n → ℂ) (v : Fin P → n → ℂ) (W : Matrix (Fin P) (Fin P) ℝ) :
    Set ℝ :=
  {t | ∃ c : Fin P → n → ℂ, (∀ i j, star (c i) ⬝ᵥ c j = if i = j then 1 else 0) ∧
      (∀ i, star (c i) ⬝ᵥ ψ = 0) ∧ (frameMatrix v c).det ≠ 0 ∧
      t = (W * ((frameMatrix v c)ᵀ * frameMatrix v c)⁻¹).trace}

end MultiParamQEC



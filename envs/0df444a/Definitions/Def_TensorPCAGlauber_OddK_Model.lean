-- Prove2me | Definitions.Def_TensorPCAGlauber_OddK_Model
-- name    : TensorPCAGlauber_OddK_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:53:31.950455+00:00
-- url     : https://prove2.me/theorems/48dd32f6-38ce-4b0d-afa7-21cfd071ac4e
-- title:
--   Spiked tensor model, tensor PCA Hamiltonian $H$ and $H_0$, average gradient and Hessian, $\zeta$, $\alpha_N$, $\sigma_N^2$ (eqs. (1), (3)–(4), (18)–(19))
-- statement:
--   Fix integers $k\ge3$, $N\ge1$. Let $G'$ be a $k$-tensor on $\mathbb R^N$ (indexed by $[N]^k$) with i.i.d. $N(0,1)$ entries and let $G$ be its symmetrization, the average of $G'_{i_{\sigma(1)}\dots i_{\sigma(k)}}$ over the $k!$ permutations $\sigma$: the standard symmetrized Gaussian tensor. For $\lambda\ge0$ and a planted $x^\star\in\Omega_N$ with $\theta^\star=x^\star/\sqrt N$, the observation is (eq. (1))
--   $$Y=\lambda\sqrt N(\theta^\star)^{\otimes k}+G,$$
--   and the tensor PCA Hamiltonian, the Ising pure $k$-spin Hamiltonian (eqs. (3)–(4)) are
--   $$H(x)=N^{-(k-1)/2}\langle Y,x^{\otimes k}\rangle,\qquad H_0(x)=N^{-(k-1)/2}\langle G,x^{\otimes k}\rangle .$$
--   For a potential $V:\Omega_N\to\mathbb R$, $u_V=E_\pi[\nabla_\Omega V]$ is the average discrete gradient and $A_V=E_\pi[\nabla^2_\Omega V]$ the average discrete Hessian; $\zeta=E_\pi[\nabla_\Omega H_0]$. Finally $\sigma_N^2=N^{-k}E_{z\sim\pi}[(\sum_iz_i)^{k+1}]$ (eq. (19)) and $\alpha_N=N^{-k-1/2}E_{z\sim\pi}[(\sum_iz_i)^{k+1}]$ (eq. (18)).
--
--   **Formalization Note.** The Gaussian tensor is `symmetrize G'` with `G'` drawn from `disorderMeasure k N` (`Measure.pi` of `gaussianReal 0 1` over `Fin k → Fin N`); every random quantity of the model is a function of `G'`. $H$ is written with the paper's scaling, so $H=N\lambda m^k+H_0$ holds identically. `KTensor k N = (Fin k → Fin N) → ℝ`.
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), p. 1 (PDF 4), eq. (1); pp. 8–9 (PDF 11–12), eqs. (3)–(5); pp. 22–23 (PDF 25–26), Theorem 4.1 and eqs. (18)–(19)

import Mathlib
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- An order-`k` tensor on `ℝ^N`, i.e. an array indexed by `[N]^k` (`Fin k → Fin N`). -/
abbrev KTensor (k N : ℕ) := (Fin k → Fin N) → ℝ

/-- The law of the raw Gaussian tensor `G'`: i.i.d. `N(0,1)` entries indexed by `[N]^k`. -/
noncomputable def disorderMeasure (k N : ℕ) : Measure (KTensor k N) :=
  Measure.pi fun _ => gaussianReal 0 1

/-- The symmetrization of a `k`-tensor: the average over the `k!` permutations of its indices.
The standard symmetrized Gaussian tensor `G` of eq. (1) is `symmetrize G'` with `G'` drawn from
`disorderMeasure k N`. -/
noncomputable def symmetrize {k N : ℕ} (G' : KTensor k N) : KTensor k N :=
  fun idx => ((Nat.factorial k : ℕ) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin k), G' (idx ∘ σ)

/-- The rank-one tensor `v^{⊗k}`, `(v^{⊗k})_{i_1…i_k} = v_{i_1} ⋯ v_{i_k}`. -/
def tensorPow {k N : ℕ} (v : Fin N → ℝ) : KTensor k N := fun idx => ∏ j, v (idx j)

/-- The Frobenius inner product `⟨A, B⟩ = ∑_{i_1…i_k} A_{i_1…i_k} B_{i_1…i_k}`. -/
def tinner {k N : ℕ} (A B : KTensor k N) : ℝ := ∑ idx, A idx * B idx

/-- `θ⋆ = x⋆/√N`. -/
noncomputable def thetaStar {N : ℕ} (xstar : Cube N) : Fin N → ℝ :=
  fun i => vec xstar i / Real.sqrt N

/-- The observed spiked tensor (eq. (1)): `Y = λ√N (θ⋆)^{⊗k} + G` with `G = symmetrize G'`. -/
noncomputable def spikedTensor (k N : ℕ) (lam : ℝ) (xstar : Cube N) (G' : KTensor k N) :
    KTensor k N :=
  fun idx => lam * Real.sqrt N * tensorPow (thetaStar xstar) idx + symmetrize G' idx

/-- The tensor PCA Hamiltonian (eq. (3)): `H(x) = N^{−(k−1)/2} ⟨Y, x^{⊗k}⟩`. -/
noncomputable def tpcaH (k N : ℕ) (lam : ℝ) (xstar : Cube N) (G' : KTensor k N)
    (x : Cube N) : ℝ :=
  (N : ℝ) ^ (-(((k : ℝ) - 1) / 2)) * tinner (spikedTensor k N lam xstar G') (tensorPow (vec x))

/-- The Ising pure `k`-spin Hamiltonian (eq. (4)): `H_0(x) = N^{−(k−1)/2} ⟨G, x^{⊗k}⟩`. -/
noncomputable def H0 (k N : ℕ) (G' : KTensor k N) (x : Cube N) : ℝ :=
  (N : ℝ) ^ (-(((k : ℝ) - 1) / 2)) * tinner (symmetrize G') (tensorPow (vec x))

/-- The average discrete gradient `u_V = E_π[∇_Ω V]` of a potential `V`. -/
noncomputable def avgGrad {N : ℕ} (V : Cube N → ℝ) : Fin N → ℝ :=
  fun i => avg fun x => pderiv i V x

/-- The average discrete Hessian `A_V = E_π[∇²_Ω V]`, `(A_V)_{ij} = E_π[∂_i ∂_j V]`. -/
noncomputable def avgHess {N : ℕ} (V : Cube N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => avg fun x => pderiv i (pderiv j V) x

/-- `ζ = E_π[∇_Ω H_0]` (Lemma 6.5; by Lemma 3.2 also `E_π[x H_0(x)]`, the form in Theorem 4.1). -/
noncomputable def zeta (k N : ℕ) (G' : KTensor k N) : Fin N → ℝ := avgGrad (H0 k N G')

/-- `σ²_N = N^{−k} E_{z∼π}[(∑_i z_i)^{k+1}]` (eq. (19)). -/
noncomputable def sigmaSq (k N : ℕ) : ℝ :=
  (N : ℝ) ^ (-(k : ℝ)) * avg fun z : Cube N => (∑ i, vec z i) ^ (k + 1)

/-- `α_N = N^{−k−1/2} E_{y∼π}[(∑_i y_i)^{k+1}]` (eq. (18)). -/
noncomputable def alphaN (k N : ℕ) : ℝ :=
  (N : ℝ) ^ (-(k : ℝ) - 1 / 2) * avg fun z : Cube N => (∑ i, vec z i) ^ (k + 1)

end TensorPCAGlauber.OddK



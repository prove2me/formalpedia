-- Prove2me | Definitions.Def_CPDNetworks_Lower_Setting
-- name    : CPDNetworks_Lower_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:11.287172+00:00
-- url     : https://prove2.me/theorems/8231575a-0842-4cd2-9a63-01c88f8118a8
-- title:
--   pp. 5–10, 34–36 — network model with missing links, its finite law, 𝒮_n(ω_n), 𝒲^τ_{n,T}(ω_n, r), type I/II errors, Matrix CUSUM, C_η, ε_n, ρ̃_n, μ_n
-- statement:
--   This file fixes the model and the objects of Enikeeva and Klopp's change-point problem for a dynamic network with missing links, together with the constants of the proof of their lower bound (Theorem 2).
--
--   **Observations.** There are $n$ vertices and $T$ time points. At time $t$ one observes a symmetric matrix $Y^t\in\{0,1\}^{n\times n}$ with zero diagonal, $Y^t_{ij}=\Omega^t_{ij}A^t_{ij}$, where $A^t$ is the adjacency matrix of the network and $\Omega^t$ indicates which pairs were sampled. The entries $Y^t_{ij}$, $i<j$, are independent over pairs and over time, with
--   $$Y^t_{ij}\sim\mathrm{Bernoulli}\big(B^t_{ij}\big),\qquad B^t=\Pi\odot\Theta^t,$$
--   where $\Theta^t$ is the matrix of connection probabilities, $\Pi$ the matrix of sampling probabilities and $\odot$ the entrywise (Hadamard) product. The law $\mathrm P_B$ of $Y=(Y^1,\dots,Y^T)$ is a finite product of Bernoulli laws, and $\mathrm P_B(E)$ is the sum of the product weights over the observations in $E$.
--
--   **Classes.** $\mathcal C_n$ is the set of symmetric matrices with entries in $[0,1]$, and $\mathcal C_n^0$ those of them with zero diagonal. Sampling matrices are those $\Pi\in\mathcal C_n$ with $\Pi_{ii}=1$ and $\Pi_{ij}>0$ for all $i,j$. With the column norm $\|M\|_{1,\infty}=\max_j\sum_i|M_{ij}|$,
--   $$\mathcal S_n(\omega_n)=\{(\Theta,\Pi):\Theta\in\mathcal C_n^0,\ \Pi\text{ a sampling matrix},\ \|\Pi\odot\Theta\|_{1,\infty}\le\omega_n\},$$
--   and, with $q(x)=\sqrt{x(1-x)}$ and the spectral norm $\|\cdot\|_{2\to2}$,
--   $$\mathcal W^\tau_{n,T}(\omega_n,r)=\{\{(\Theta^a,\Pi),(\Theta^b,\Pi)\}:(\Theta^a,\Pi),(\Theta^b,\Pi)\in\mathcal S_n(\omega_n),\ q(\tau/T)\,\|\Pi\odot(\Theta^a-\Theta^b)\|_{2\to2}\ge r\}.$$
--   Under $H_0$ every $B^t$ equals $\Pi\odot\Theta^0$; under the alternative with change at $\tau$, $B^t=\Pi\odot\Theta^b$ for $1\le t\le\tau$ and $B^t=\Pi\odot\Theta^a$ for $\tau<t\le T$.
--
--   **Errors (Definition 1).** For a test $\psi$ (a $\{0,1\}$-valued function of $Y$) the type I error is
--   $$\alpha(\psi)=\sup_{(\Theta^0,\Pi)\in\mathcal S_n(\omega_n)}\mathrm P_{(\Theta^0,\Pi)}\{\psi=1\},$$
--   and for a set $\mathcal D$ of change points the type II error is
--   $$\beta(\psi,R)=\sup_{\tau\in\mathcal D}\ \sup_{\mathcal W^\tau_{n,T}(\omega_n,R)}\mathrm P\{\psi=0\}.$$
--   Problem (P1) is $\mathcal D=\{\tau\}$.
--
--   **Matrix CUSUM (6).** $Z_T(t)=\sqrt{t(T-t)/T}\,\big(\tfrac1t\sum_{s=1}^tY^s-\tfrac1{T-t}\sum_{s=t+1}^TY^s\big)$.
--
--   **Constants of the lower bound.** With $\eta=\alpha+\beta$,
--   $$C_\eta=\log\big(1+4(1-\eta)^2\big),\qquad \varepsilon_n=(2C_\eta)^{1/4}\omega_n^{-1/2},\qquad \tilde\rho_n=(1-\varepsilon_n)\frac{\omega_n}{n-1},$$
--   $$\mu_n=\frac{TR^2}{\omega_n}\cdot\frac{1}{(1-\tilde\rho_n)(n-1)(1-\varepsilon_n)}.$$
--   A sign vector $\zeta\in\{-1,+1\}^n$ is encoded by a Boolean vector, and the expectation $\mathrm E_\zeta$ over i.i.d. Rademacher signs is the average $2^{-n}\sum_\zeta$.
--
--   These are the objects every statement of the mission refers to.
--
--   **Formalization Note** The observation space is finite: an observation is a Boolean for each time point (0-based, so Lean time $t$ is the paper's time $t+1$) and each pair $i<j$. Only $Y$ is observed, so the latent $A^t$ and $\Omega^t$ are integrated out; the paper's tests and likelihoods (p. 35) use only $Y^t_{ij}\sim\mathrm{Bernoulli}(\Pi_{ij}\Theta^t_{ij})$. Probabilities are finite sums of products of Bernoulli weights, so no measure theory is needed and every test (a Boolean function of the observation) is measurable. The sampling class carries the standing assumptions of §2, p. 5 ($\Pi_{ii}=1$, $\Pi_{ij}>0$). The errors are real suprema (`sSup`) of sets of probabilities, which are bounded in $[0,1]$; an empty alternative class gives type II error $0$, the paper's convention, which can only make a lower bound on the type II error harder. The spectral norm is the published `HighDimProb.RandomMatrices.matrixOpNorm`. All of $C_\eta$, $\varepsilon_n$, $\tilde\rho_n$, $\mu_n$ are real-valued; the theorems that use them carry the hypotheses ($n\ge2$, $\omega_n>0$, $\eta\le1$) under which they are the paper's quantities.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, pp. 5–10 (§2–3, (1)–(3), (6), Definition 1), pp. 34–36 (proof of Theorem 2: ρ̃_n, ε_n, μ_n)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm

namespace CPDNetworks.Lower

open scoped Matrix
open HighDimProb.RandomMatrices

/-- Unordered pairs `{i, j}` of distinct vertices, encoded as `i < j` (Enikeeva–Klopp, p. 5). -/
abbrev Pair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- An observation of the dynamic network: for each of the `T` snapshots (0-based time, `t : Fin T`
is the paper's time `t + 1`) and each pair `i < j`, whether the edge `{i, j}` was observed present,
`Y^t_ij = Ω^t_ij A^t_ij ∈ {0, 1}` (p. 5, model (1)). -/
abbrev Obs (n T : ℕ) := Fin T → Pair n → Bool

/-- The observed adjacency matrix `Y^t`: symmetric, zero diagonal, entries in `{0, 1}`. -/
noncomputable def obsMat {n T : ℕ} (y : Obs n T) (t : Fin T) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if h : i < j then (if y t ⟨(i, j), h⟩ then 1 else 0)
    else if h' : j < i then (if y t ⟨(j, i), h'⟩ then 1 else 0)
    else 0

/-- Bernoulli mass function: probability `p` of `true`, `1 - p` of `false`. -/
def bern (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- Probability of the observation `y` when the entries `Y^t_ij`, `i < j`, are independent
Bernoulli with success probabilities `B^t_ij` (`B^t = Π ⊙ Θ^t`, p. 6). -/
noncomputable def weight {n T : ℕ} (B : Fin T → Matrix (Fin n) (Fin n) ℝ) (y : Obs n T) : ℝ :=
  ∏ t, ∏ p : Pair n, bern (B t p.1.1 p.1.2) (y t p)

open Classical in
/-- The probability of an event `E` of the observations under the law with observed-edge
probability matrices `B^1, …, B^T` (a finite sum over the finite observation space). -/
noncomputable def prob {n T : ℕ} (B : Fin T → Matrix (Fin n) (Fin n) ℝ) (E : Obs n T → Prop) : ℝ :=
  ∑ y, if E y then weight B y else 0

/-- `𝒞_n`: symmetric matrices with entries in `[0, 1]` (p. 5). -/
def IsConnProb {n : ℕ} (Θ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Θ.IsSymm ∧ ∀ i j, 0 ≤ Θ i j ∧ Θ i j ≤ 1

/-- `𝒞⁰_n`: matrices of `𝒞_n` with zero diagonal (p. 5). -/
def IsConnProb0 {n : ℕ} (Θ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsConnProb Θ ∧ ∀ i, Θ i i = 0

/-- Sampling matrices: `Π ∈ 𝒞_n` with the standing assumptions of §2, p. 5: `Π_ii = 1` and
`Π_ij > 0` for every pair. -/
def IsSampling {n : ℕ} (Pm : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsConnProb Pm ∧ (∀ i, Pm i i = 1) ∧ ∀ i j, 0 < Pm i j

/-- The column-wise `‖·‖_{1,∞}` norm: the largest absolute column sum (p. 6). -/
noncomputable def norm1inf {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ j, ∑ i, |M i j|

/-- `(Θ, Π) ∈ 𝒮_n(ω_n)`, display (2), p. 6. -/
def InS {n : ℕ} (ω : ℝ) (Θ Pm : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsConnProb0 Θ ∧ IsSampling Pm ∧ norm1inf (Pm ⊙ Θ) ≤ ω

/-- `q(x) = √(x(1 - x))` (p. 5). -/
noncomputable def q (x : ℝ) : ℝ := Real.sqrt (x * (1 - x))

/-- `{(Θ^a, Π), (Θ^b, Π)} ∈ 𝒲^τ_{n,T}(ω_n, r)`, display (3), p. 7: both pairs in `𝒮_n(ω_n)` and
change-point energy `q(τ/T) ‖Π ⊙ (Θ^a − Θ^b)‖_{2→2} ≥ r`. -/
def InW {n : ℕ} (T τ : ℕ) (ω r : ℝ) (Θa Θb Pm : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  InS ω Θa Pm ∧ InS ω Θb Pm ∧ r ≤ q ((τ : ℝ) / T) * matrixOpNorm (Pm ⊙ (Θa - Θb))

/-- The null law `P_(Θ⁰, Π)`: every snapshot has observed-edge probabilities `Π ⊙ Θ⁰`. -/
def nullParam {n T : ℕ} (Θ Pm : Matrix (Fin n) (Fin n) ℝ) : Fin T → Matrix (Fin n) (Fin n) ℝ :=
  fun _ => Pm ⊙ Θ

/-- The alternative law `P_(Θ⁰+ΔΘ^τ, Π), (Θ⁰, Π)` (p. 8): `Π ⊙ Θ^b` (with `Θ^b = Θ⁰`) at the
paper's times `1, …, τ` (0-based `t < τ`), and `Π ⊙ Θ^a` (with `Θ^a = Θ⁰ + ΔΘ^τ`) afterwards. -/
def altParam {n T : ℕ} (τ : ℕ) (Θa Θb Pm : Matrix (Fin n) (Fin n) ℝ) :
    Fin T → Matrix (Fin n) (Fin n) ℝ :=
  fun t => if (t : ℕ) < τ then Pm ⊙ Θb else Pm ⊙ Θa

/-- Type I error of a test `ψ` (Definition 1, p. 9): the supremum over `(Θ⁰, Π) ∈ 𝒮_n(ω_n)` of
`P_(Θ⁰, Π){ψ = 1}`. -/
noncomputable def typeI {n T : ℕ} (ω : ℝ) (ψ : Obs n T → Bool) : ℝ :=
  sSup {p | ∃ Θ Pm, InS ω Θ Pm ∧ p = prob (nullParam (T := T) Θ Pm) (fun y => ψ y = true)}

/-- Type II error of a test `ψ` (Definition 1, p. 9) over the change-point locations `D`: the
supremum over `τ ∈ D` and over `𝒲^τ_{n,T}(ω_n, R)` of `P_(Θ⁰+ΔΘ^τ, Π), (Θ⁰, Π){ψ = 0}`. -/
noncomputable def typeII {n T : ℕ} (D : Finset ℕ) (ω R : ℝ) (ψ : Obs n T → Bool) : ℝ :=
  sSup {p | ∃ τ ∈ D, ∃ Θa Θb Pm, InW T τ ω R Θa Θb Pm ∧
    p = prob (altParam τ Θa Θb Pm) (fun y => ψ y = false)}

/-- The Matrix CUSUM statistic `Z_T(t)`, display (6), p. 7 (0-based snapshots `s < t` are the
paper's `s = 1, …, t`). -/
noncomputable def cusum {n T : ℕ} (y : Obs n T) (t : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Real.sqrt (t * ((T : ℝ) - t) / T) •
    ((t : ℝ)⁻¹ • ∑ s ∈ Finset.univ.filter (fun s : Fin T => (s : ℕ) < t), obsMat y s -
      ((T : ℝ) - t)⁻¹ • ∑ s ∈ Finset.univ.filter (fun s : Fin T => t ≤ (s : ℕ)), obsMat y s)

/-- The constant `C_η = log(1 + 4(1 − η)²)` with `η = α + β` (p. 10). -/
noncomputable def Ceta (α β : ℝ) : ℝ := Real.log (1 + 4 * (1 - (α + β)) ^ 2)

/-- `ε_n = (2C_η)^{1/4} ω_n^{−1/2}` (proof of Theorem 2, Step 1, p. 35). -/
noncomputable def epsN (α β ω : ℝ) : ℝ := (2 * Ceta α β) ^ (1 / 4 : ℝ) / Real.sqrt ω

/-- `ρ̃_n = (1 − ε_n) ω_n / (n − 1)` (proof of Theorem 2, Step 1, p. 34). -/
noncomputable def rhoTilde (n : ℕ) (α β ω : ℝ) : ℝ := (1 - epsN α β ω) * ω / ((n : ℝ) - 1)

/-- `μ_n = (T R²_{n,τ} / ω_n) · 1 / ((1 − ρ̃_n)(n − 1)(1 − ε_n))` (proof of Theorem 2, Step 3,
p. 36). -/
noncomputable def muN (n T : ℕ) (ω α β R : ℝ) : ℝ :=
  (T : ℝ) * R ^ 2 / ω * (1 / ((1 - rhoTilde n α β ω) * ((n : ℝ) - 1) * (1 - epsN α β ω)))

/-- The sign vector `ζ ∈ {−1, +1}ⁿ` encoded by `b : Fin n → Bool` (`true ↦ +1`, `false ↦ −1`);
the uniform (Rademacher) law on `{−1, +1}ⁿ` is the average `2^{−n} Σ_b` over all `b`. -/
def sgn {n : ℕ} (b : Fin n → Bool) (i : Fin n) : ℝ := if b i then 1 else -1

end CPDNetworks.Lower



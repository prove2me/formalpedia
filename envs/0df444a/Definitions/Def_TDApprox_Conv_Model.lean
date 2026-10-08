-- Prove2me | Definitions.Def_TDApprox_Conv_Model
-- name    : TDApprox_Conv_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:08.273267+00:00
-- url     : https://prove2.me/theorems/26abf4dc-0a7e-43ef-b3db-8a374987c7ca
-- title:
--   §§2–6, pp. 4–19 — the Markov chain and its path law, J*, ḡ, L₂(S, D), Π, T^(λ), the TD(λ) iterates, Assumptions 1–4, the stationary chain of (5), s(r, X), A(X), b(X)
-- statement:
--   This file sets up the objects of Tsitsiklis and Van Roy's analysis of temporal-difference learning with linear function approximation.
--
--   **Chain and costs.** The state space $S$ is a finite or countably infinite set with the discrete $\sigma$-algebra. The chain $i_0, i_1, \dots$ moves according to a transition matrix $P = (p_{ij})$, viewed as a Markov kernel; $P^m$ is its $m$-step power. A transition from $i$ to $j$ costs $g(i,j)$, and $\alpha \in (0,1)$ is a discount factor. For an initial law $\mu_0$ (or an initial state $i$), the law of the path $(i_t)_{t \ge 0}$ is built by the Ionescu–Tulcea construction; $E[\,\cdot \mid i_0 = i]$ denotes expectation under this path law. Further,
--   $$(PJ)(i) = \sum_j p_{ij} J(j), \qquad \bar g(i) = E[g(i_t,i_{t+1}) \mid i_t = i] = \sum_j p_{ij}\, g(i,j),$$
--   and the cost-to-go is the path expectation
--   $$J^*(i) = E\Big[\sum_{t=0}^\infty \alpha^t g(i_t,i_{t+1}) \,\Big|\, i_0 = i\Big].$$
--
--   **Weighted space and projection.** For a probability vector $\pi$ on $S$ (the steady-state distribution, with $D = \mathrm{diag}(\pi)$), $L_2(S,D)$ is the set of $J$ with $\|J\|_D^2 = \sum_i \pi(i) J(i)^2 < \infty$. With basis functions $\phi_1,\dots,\phi_K$ and $\phi(i) = (\phi_1(i),\dots,\phi_K(i))$, the approximation is $\tilde J(r) = \Phi' r$, i.e. $\tilde J(i,r) = r'\phi(i)$. The projection onto $\{\Phi' r\}$ in $\langle\cdot,\cdot\rangle_D$ is Eq. (1),
--   $$\Pi = \Phi'(\Phi D \Phi')^{-1}\Phi D,$$
--   with $(\Phi D\Phi')_{kl} = \sum_i \pi(i)\phi_k(i)\phi_l(i)$ and $(\Phi D J)_k = \sum_i \pi(i)\phi_k(i)J(i)$. The matrices $\Phi D P^m \Phi'$ and vectors $\Phi D P^m \bar g$ are defined entrywise in the same way.
--
--   **The operator $T^{(\lambda)}$.** For $\lambda \in [0,1)$,
--   $$(T^{(\lambda)}J)(i) = (1-\lambda)\sum_{m=0}^\infty \lambda^m E\Big[\sum_{t=0}^m \alpha^t g(i_t,i_{t+1}) + \alpha^{m+1}J(i_{m+1}) \,\Big|\, i_0 = i\Big],$$
--   and $T^{(1)}J = J^*$.
--
--   **TD($\lambda$).** Along a path $(i_t)$, with step sizes $\gamma_t$ and an arbitrary $r_0$, the eligibility vectors are $z_t = \sum_{k=0}^t (\alpha\lambda)^{t-k}\phi(i_k)$, the temporal differences are $d_t = g(i_t,i_{t+1}) + \alpha\phi(i_{t+1})'r_t - \phi(i_t)'r_t$, and $r_{t+1} = r_t + \gamma_t d_t z_t$.
--
--   **Assumptions.**
--   1. (a) $\pi$ is the unique invariant distribution ($\pi'P = \pi'$) and $\pi(i) > 0$ for all $i$; (b) $E_0[g^2(i_t,i_{t+1})] < \infty$; (c) for every $i$, the expectation defining $J^*(i)$ is well defined and finite.
--   2. (a) $\phi_1,\dots,\phi_K$ are linearly independent; (b) $E_0[\phi_k^2(i)] < \infty$ for every $k$.
--   3. With $\sigma(i) \in \mathbb R^N$ the coordinates of state $i$: (a) for every $q > 1$ there is $\mu_q$ with $E[\|\sigma(i_t)\|^q \mid i_0] \le \mu_q(1 + \|\sigma(i_0)\|^q)$ for all $i_0, t$; (b) there are $C_1, q_1 > 0$ with $\|\phi(i)\| \le C_1(1+\|\sigma(i)\|^{q_1})$ and $|g(i,j)| \le C_1(1 + \|\sigma(i)\|^{q_1} + \|\sigma(j)\|^{q_1})$; (c) there are $C_2, q_2 > 0$ such that for all $i_0$ and $m \ge 0$ the expectations involved are finite and
--   $$\sum_{\tau=0}^\infty \big\|E[\phi(i_\tau)\phi'(i_{\tau+m}) \mid i_0] - E_0[\phi(i_0)\phi'(i_m)]\big\| \le C_2(1+\|\sigma(i_0)\|^{q_2}),$$
--   $$\sum_{\tau=0}^\infty \big\|E[\phi(i_\tau)g(i_{\tau+m},i_{\tau+m+1}) \mid i_0] - E_0[\phi(i_0)g(i_m,i_{m+1})]\big\| \le C_2(1+\|\sigma(i_0)\|^{q_2}).$$
--   4. The step sizes are predetermined, nonnegative and nonincreasing, with $\sum_t \gamma_t = \infty$ and $\sum_t \gamma_t^2 < \infty$.
--
--   **Steady state (§5).** A two-sided chain $(i_t)_{t\in\mathbb Z}$ on a probability space is *stationary* if $\Pr(i_a = s_0, \dots, i_{a+n} = s_n) = \pi(s_0)p_{s_0s_1}\cdots p_{s_{n-1}s_n}$ for all $a, n, s_0, \dots, s_n$. For such a chain, Eq. (5) sets $z_t = \sum_{\tau=-\infty}^t (\alpha\lambda)^{t-\tau}\phi(i_\tau)$ and $X_t = (i_t, i_{t+1}, z_t)$. For $X = (i,j,z)$,
--   $$s(r,X) = \big(g(i,j) + \alpha\tilde J(j,r) - \tilde J(i,r)\big)z, \qquad A(X) = z\big(\alpha\phi'(j) - \phi'(i)\big), \qquad b(X) = z\,g(i,j),$$
--   so that $s(r,X) = A(X)r + b(X)$. Finally, for a general Markov process $X_t$ and matrix and vector functions $A(\cdot), b(\cdot)$, the stochastic approximation iterates are $r_{t+1} = r_t + \gamma_t(A(X_t)r_t + b(X_t))$.
--
--   These are the objects in which Theorem 1 and Lemmas 1–8 are stated.
--
--   **Formalization Note.** $S$ is a countable type with the discrete $\sigma$-algebra, $P$ a Markov kernel with $p_{ij} = P(i)(\{j\})$, and $P^m$ the kernel power. The path law is Mathlib's `Kernel.trajMeasure` applied to the time-homogeneous kernels. $J^*$ and $T^{(\lambda)}$ are defined by the path expectations of pp. 4 and 6, not by the matrix series of Lemmas 2 and 3. Lean's Bochner integral is $0$ for non-integrable integrands and `tsum` is $0$ for non-summable families, so every theorem that uses these objects states the integrability or summability it needs. $L_2(S,D)$ membership is summability of $\pi(i)J(i)^2$. $(\Phi D\Phi')^{-1}$ is `Matrix.inv`, which is $0$ for a singular matrix; it is used only under Assumptions 1(a) and 2, where $\Phi D \Phi'$ is positive definite. Assumption 1(c) is read as absolute integrability, $E[\sum_t \alpha^t|g(i_t,i_{t+1})| \mid i_0 = i] < \infty$. Moment hypotheses are `Integrable` statements. Vector norms are Euclidean. Matrix norms are Frobenius norms, which are equivalent to the paper's Euclidean induced norm up to a factor $\sqrt K$; each such norm sits under an existential constant, so the change is harmless. The stationary $E_0$ in Assumption 3(c) is taken at time $0$, which by stationarity equals the page's time-$t$ value; in the second sum the page prints $E_0[\phi(i_t)g(i_{\tau+m}, i_{\tau+m+1})]$, which mixes $t$ and $\tau$, and the intended $E_0[\phi(i_0)g(i_m,i_{m+1})]$ is used. In Eq. (5) the sum is written as $\sum_{\tau \ge 0}(\alpha\lambda)^\tau \phi(i_{t-\tau})$. The objects take an arbitrary measurable space on $S$; every statement that uses them assumes $S$ countable with the discrete $\sigma$-algebra. Assumption 1(a) records invariance, uniqueness among probability measures and positivity; that $\pi$ is itself a probability measure is a separate hypothesis carried by every statement that uses it. The location map $\sigma$ of Assumption 3 is not required to be injective: an injective $\sigma'(i) = (\sigma(i), \varepsilon_i)$ with distinct $\varepsilon_i \in (0,1)$ satisfies Assumption 3 whenever $\sigma$ does, with other constants, so nothing is gained or lost.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), §2 pp. 4–5, §3 p. 6 Eq. (1) and p. 7 (s(r, X)), §4 Assumptions 1–4 pp. 9–11, §5 p. 15 Eq. (5), §6 pp. 18–19 (A(X), b(X)), Theorem 2 p. 18 (the iteration)

import Mathlib

namespace TDApprox.Conv

open MeasureTheory ProbabilityTheory Finset Matrix

/-! # Tsitsiklis & Van Roy (LIDS-P-2322, 1996), §§2–5: the model of TD(λ) with linear function
approximation

States form a countable type `S` with the discrete σ-algebra (§2, p. 4: "a finite or countably
infinite" state space indexed by positive integers). The transition matrix `P` is a Markov kernel
on `S`, with `p_ij = (P i {j}).toReal`; the `m`-step matrix `P^m` is the kernel power `P ^ m`. -/

section Chain

variable {S : Type*} [MeasurableSpace S]

/-- The time-homogeneous kernel used at step `n` of the Ionescu–Tulcea construction: the law of
`i_{n+1}` given `(i_0, …, i_n)` is `P (i_n)`. -/
noncomputable def stepKernel (P : Kernel S S) (n : ℕ) : Kernel (Π _ : Iic n, S) S :=
  P.comap (fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance stepKernel.isMarkovKernel (P : Kernel S S) [IsMarkovKernel P] (n : ℕ) :
    IsMarkovKernel (stepKernel P n) := by
  unfold stepKernel; infer_instance

/-- The law on paths `ω : ℕ → S` (`ω t = i_t`) of the Markov chain with transition kernel `P` and
initial law `μ₀` (Ionescu–Tulcea). -/
noncomputable def pathLawFrom (P : Kernel S S) [IsMarkovKernel P] (μ₀ : Measure S) :
    Measure (ℕ → S) :=
  Kernel.trajMeasure (X := fun _ => S) μ₀ (stepKernel P)

instance pathLawFrom.isProbabilityMeasure (P : Kernel S S) [IsMarkovKernel P] (μ₀ : Measure S)
    [IsProbabilityMeasure μ₀] : IsProbabilityMeasure (pathLawFrom P μ₀) := by
  unfold pathLawFrom; infer_instance

/-- The law on paths of the Markov chain started at the state `i` (`i_0 = i`). Expectations
`E[· | i_0 = i]` are integrals against this measure. -/
noncomputable def pathLaw (P : Kernel S S) [IsMarkovKernel P] (i : S) : Measure (ℕ → S) :=
  pathLawFrom P (Measure.dirac i)

instance pathLaw.isProbabilityMeasure (P : Kernel S S) [IsMarkovKernel P] (i : S) :
    IsProbabilityMeasure (pathLaw P i) := by
  unfold pathLaw; infer_instance

/-- `(PJ)(i) = E[J(i_1) | i_0 = i] = Σ_j p_ij J(j)`. -/
noncomputable def Pop (P : Kernel S S) (J : S → ℝ) : S → ℝ :=
  fun i => ∫ j, J j ∂(P i)

/-- `ḡ(i) = E[g(i_t, i_{t+1}) | i_t = i] = Σ_j p_ij g(i, j)` (p. 12). -/
noncomputable def gbar (P : Kernel S S) (g : S → S → ℝ) : S → ℝ :=
  fun i => ∫ j, g i j ∂(P i)

/-- The cost-to-go `J*(i) = E[Σ_{t≥0} α^t g(i_t, i_{t+1}) | i_0 = i]` (p. 4), as an expectation
over the path law. -/
noncomputable def Jstar (P : Kernel S S) [IsMarkovKernel P] (g : S → S → ℝ) (α : ℝ) : S → ℝ :=
  fun i => ∫ ω, ∑' t, α ^ t * g (ω t) (ω (t + 1)) ∂(pathLaw P i)

/-- The operator `T^(λ)` (p. 6). For `λ ∈ [0, 1)`,
`(T^(λ)J)(i) = (1 − λ) Σ_{m≥0} λ^m E[Σ_{t=0}^m α^t g(i_t, i_{t+1}) + α^{m+1} J(i_{m+1}) | i_0 = i]`;
for `λ = 1`, `T^(1)J = J*`. -/
noncomputable def Tlam (P : Kernel S S) [IsMarkovKernel P] (g : S → S → ℝ) (α lam : ℝ)
    (J : S → ℝ) : S → ℝ :=
  if lam = 1 then Jstar P g α else fun i =>
    (1 - lam) * ∑' m : ℕ, lam ^ m *
      ∫ ω, (∑ t ∈ range (m + 1), α ^ t * g (ω t) (ω (t + 1)) + α ^ (m + 1) * J (ω (m + 1)))
        ∂(pathLaw P i)

end Chain

/-! ## The weighted space `L₂(S, D)` and the projection `Π` (§3, p. 6) -/

section L2

variable {S : Type*} [MeasurableSpace S]

/-- `J ∈ L₂(S, D)`: `‖J‖_D² = Σ_i π(i) J(i)² < ∞`. -/
def MemL2D (π : Measure S) (J : S → ℝ) : Prop :=
  Summable (fun i => (π {i}).toReal * J i ^ 2)

/-- `‖J‖_D = √(Σ_i π(i) J(i)²)`. -/
noncomputable def normD (π : Measure S) (J : S → ℝ) : ℝ :=
  Real.sqrt (∑' i, (π {i}).toReal * J i ^ 2)

variable {K : ℕ}

/-- `J̃(r) = Φ′r`, i.e. `J̃(i, r) = r′φ(i) = Σ_k r(k) φ_k(i)`. -/
def Jtilde (φ : S → Fin K → ℝ) (r : Fin K → ℝ) : S → ℝ :=
  fun i => φ i ⬝ᵥ r

/-- The `K × K` matrix `ΦDΦ′`, with entries `Σ_i π(i) φ_k(i) φ_l(i)`. -/
noncomputable def gram (π : Measure S) (φ : S → Fin K → ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  fun k l => ∑' i, (π {i}).toReal * φ i k * φ i l

/-- The vector `ΦDJ ∈ ℝ^K`, with entries `Σ_i π(i) φ_k(i) J(i)`. -/
noncomputable def phiD (π : Measure S) (φ : S → Fin K → ℝ) (J : S → ℝ) : Fin K → ℝ :=
  fun k => ∑' i, (π {i}).toReal * φ i k * J i

/-- The projection `Π = Φ′(ΦDΦ′)^{-1}ΦD` of Eq. (1). -/
noncomputable def proj (π : Measure S) (φ : S → Fin K → ℝ) (J : S → ℝ) : S → ℝ :=
  Jtilde φ ((gram π φ)⁻¹ *ᵥ phiD π φ J)

/-- The `K × K` matrix `ΦDP^mΦ′`, with entries `Σ_i π(i) φ_k(i) (P^m φ_l)(i)` (p. 15). -/
noncomputable def phiDPmPhi (P : Kernel S S) (π : Measure S) (φ : S → Fin K → ℝ) (m : ℕ) :
    Matrix (Fin K) (Fin K) ℝ :=
  fun k l => ∑' i, (π {i}).toReal * φ i k * ∫ j, φ j l ∂((P ^ m) i)

/-- The vector `ΦDP^m ḡ ∈ ℝ^K`, with entries `Σ_i π(i) φ_k(i) (P^m ḡ)(i)`. -/
noncomputable def phiDPmGbar (P : Kernel S S) (π : Measure S) (φ : S → Fin K → ℝ)
    (g : S → S → ℝ) (m : ℕ) : Fin K → ℝ :=
  fun k => ∑' i, (π {i}).toReal * φ i k * ∫ j, gbar P g j ∂((P ^ m) i)

end L2

/-! ## Euclidean and Frobenius norms -/

/-- The Euclidean norm `√(Σ_k v_k²)` of a vector of `ℝ^n`. -/
noncomputable def euclNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ k, v k ^ 2)

/-- The Frobenius norm `√(Σ_{k,l} M_{kl}²)` of a square matrix (equivalent to the Euclidean
induced norm: `‖M‖₂ ≤ ‖M‖_F ≤ √n ‖M‖₂`). -/
noncomputable def frobNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ k, ∑ l, M k l ^ 2)

/-! ## The TD(λ) iterates (§2, p. 5) -/

section TD

variable {S : Type*} {K : ℕ}

/-- The eligibility vector `z_t = Σ_{k=0}^t (αλ)^{t−k} φ(i_k)` along the path `ω` (`i_t = ω t`). -/
def elig (α lam : ℝ) (φ : S → Fin K → ℝ) (ω : ℕ → S) (t : ℕ) : Fin K → ℝ :=
  ∑ k ∈ range (t + 1), (α * lam) ^ (t - k) • φ (ω k)

/-- The TD(λ) iterates along the path `ω`: `r_0` given and
`r_{t+1} = r_t + γ_t d_t z_t` with `d_t = g(i_t, i_{t+1}) + α φ(i_{t+1})′r_t − φ(i_t)′r_t`. -/
def tdIter (α lam : ℝ) (γ : ℕ → ℝ) (g : S → S → ℝ) (φ : S → Fin K → ℝ) (r₀ : Fin K → ℝ)
    (ω : ℕ → S) : ℕ → Fin K → ℝ
  | 0 => r₀
  | t + 1 =>
    tdIter α lam γ g φ r₀ ω t +
      (γ t * (g (ω t) (ω (t + 1)) + α * (φ (ω (t + 1)) ⬝ᵥ tdIter α lam γ g φ r₀ ω t)
        - φ (ω t) ⬝ᵥ tdIter α lam γ g φ r₀ ω t)) • elig α lam φ ω t

end TD

/-! ## Assumptions 1–4 (§4, pp. 9–11) -/

section Assumptions

variable {S : Type*} [MeasurableSpace S] {K : ℕ}

/-- Assumption 1(a): `π` is the unique invariant distribution of the chain (`π′P = π′`), and
`π(i) > 0` for every `i`. -/
structure Assumption1a (P : Kernel S S) (π : Measure S) : Prop where
  invariant : P.Invariant π
  unique : ∀ ν : Measure S, IsProbabilityMeasure ν → P.Invariant ν → ν = π
  pos : ∀ i, 0 < π {i}

/-- Assumption 1(b): `E_0[g²(i_t, i_{t+1})] < ∞`, the expectation under the stationary law of a
transition `(i_t, i_{t+1}) ~ π ⊗ P`. -/
def Assumption1b (P : Kernel S S) (π : Measure S) (g : S → S → ℝ) : Prop :=
  Integrable (fun x : S × S => g x.1 x.2 ^ 2) (π ⊗ₘ P)

/-- Assumption 1(c): for every `i`, the expectation defining `J*(i)` is well defined and finite
(absolute integrability: `E[Σ_t α^t |g(i_t, i_{t+1})| | i_0 = i] < ∞`). -/
def Assumption1c (P : Kernel S S) [IsMarkovKernel P] (g : S → S → ℝ) (α : ℝ) : Prop :=
  ∀ i, ∫⁻ ω, ∑' t, ENNReal.ofReal (α ^ t * |g (ω t) (ω (t + 1))|) ∂(pathLaw P i) < ⊤

/-- Assumption 1 = (a) ∧ (b) ∧ (c). -/
structure Assumption1 (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) (g : S → S → ℝ)
    (α : ℝ) : Prop where
  a : Assumption1a P π
  b : Assumption1b P π g
  c : Assumption1c P g α

/-- Assumption 2: (a) the basis functions `φ_1, …, φ_K` are linearly independent (`Φ` has full
row rank); (b) `E_0[φ_k²(i)] < ∞` for every `k`. -/
structure Assumption2 (π : Measure S) (φ : S → Fin K → ℝ) : Prop where
  linIndep : LinearIndependent ℝ (fun k : Fin K => fun i : S => φ i k)
  sq_integrable : ∀ k, Integrable (fun i => φ i k ^ 2) π

/-- `E[φ(i_τ)φ′(i_{τ+m}) | i_0]`, the `K × K` matrix of conditional cross moments. -/
noncomputable def condCorr (P : Kernel S S) [IsMarkovKernel P] (φ : S → Fin K → ℝ) (i₀ : S)
    (τ m : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  fun k l => ∫ ω, φ (ω τ) k * φ (ω (τ + m)) l ∂(pathLaw P i₀)

/-- `E_0[φ(i_0)φ′(i_m)]`, the stationary cross moment (chain started from `π`). -/
noncomputable def statCorr (P : Kernel S S) [IsMarkovKernel P] (π : Measure S)
    (φ : S → Fin K → ℝ) (m : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  fun k l => ∫ ω, φ (ω 0) k * φ (ω m) l ∂(pathLawFrom P π)

/-- `E[φ(i_τ) g(i_{τ+m}, i_{τ+m+1}) | i_0] ∈ ℝ^K`. -/
noncomputable def condCrossG (P : Kernel S S) [IsMarkovKernel P] (φ : S → Fin K → ℝ)
    (g : S → S → ℝ) (i₀ : S) (τ m : ℕ) : Fin K → ℝ :=
  fun k => ∫ ω, φ (ω τ) k * g (ω (τ + m)) (ω (τ + m + 1)) ∂(pathLaw P i₀)

/-- `E_0[φ(i_0) g(i_m, i_{m+1})] ∈ ℝ^K`. -/
noncomputable def statCrossG (P : Kernel S S) [IsMarkovKernel P] (π : Measure S)
    (φ : S → Fin K → ℝ) (g : S → S → ℝ) (m : ℕ) : Fin K → ℝ :=
  fun k => ∫ ω, φ (ω 0) k * g (ω m) (ω (m + 1)) ∂(pathLawFrom P π)

/-- Assumption 3, with `σ(i) ∈ ℝ^N` the coordinates of state `i` (p. 4).
(a) For any `q > 1` there is `μ_q` with `E[‖σ(i_t)‖^q | i_0] ≤ μ_q(1 + ‖σ(i_0)‖^q)` for all
`i_0, t`.
(b) There are `C₁, q₁ > 0` with `‖φ(i)‖ ≤ C₁(1 + ‖σ(i)‖^{q₁})` and
`|g(i, j)| ≤ C₁(1 + ‖σ(i)‖^{q₁} + ‖σ(j)‖^{q₁})`.
(c) There are `C₂, q₂ > 0` such that, for all `i_0` and `m ≥ 0`, the expectations below are
finite and
`Σ_τ ‖E[φ(i_τ)φ′(i_{τ+m}) | i_0] − E_0[φ(i_0)φ′(i_m)]‖ ≤ C₂(1 + ‖σ(i_0)‖^{q₂})`,
`Σ_τ ‖E[φ(i_τ)g(i_{τ+m}, i_{τ+m+1}) | i_0] − E_0[φ(i_0)g(i_m, i_{m+1})]‖ ≤ C₂(1 + ‖σ(i_0)‖^{q₂})`. -/
structure Assumption3 {N : ℕ} (P : Kernel S S) [IsMarkovKernel P] (π : Measure S)
    (g : S → S → ℝ) (φ : S → Fin K → ℝ) (σ : S → Fin N → ℝ) : Prop where
  a : ∀ q : ℝ, 1 < q → ∃ μq : ℝ, ∀ i t,
    Integrable (fun ω => euclNorm (σ (ω t)) ^ q) (pathLaw P i) ∧
      ∫ ω, euclNorm (σ (ω t)) ^ q ∂(pathLaw P i) ≤ μq * (1 + euclNorm (σ i) ^ q)
  b : ∃ C₁ q₁ : ℝ, 0 < C₁ ∧ 0 < q₁ ∧
    (∀ i, euclNorm (φ i) ≤ C₁ * (1 + euclNorm (σ i) ^ q₁)) ∧
    ∀ i j, |g i j| ≤ C₁ * (1 + euclNorm (σ i) ^ q₁ + euclNorm (σ j) ^ q₁)
  c : ∃ C₂ q₂ : ℝ, 0 < C₂ ∧ 0 < q₂ ∧ ∀ (i₀ : S) (m : ℕ),
    (∀ τ k l, Integrable (fun ω => φ (ω τ) k * φ (ω (τ + m)) l) (pathLaw P i₀)) ∧
    (∀ k l, Integrable (fun ω => φ (ω 0) k * φ (ω m) l) (pathLawFrom P π)) ∧
    (∀ τ k, Integrable (fun ω => φ (ω τ) k * g (ω (τ + m)) (ω (τ + m + 1))) (pathLaw P i₀)) ∧
    (∀ k, Integrable (fun ω => φ (ω 0) k * g (ω m) (ω (m + 1))) (pathLawFrom P π)) ∧
    Summable (fun τ => frobNorm (condCorr P φ i₀ τ m - statCorr P π φ m)) ∧
    ∑' τ, frobNorm (condCorr P φ i₀ τ m - statCorr P π φ m) ≤
      C₂ * (1 + euclNorm (σ i₀) ^ q₂) ∧
    Summable (fun τ => euclNorm (condCrossG P φ g i₀ τ m - statCrossG P π φ g m)) ∧
    ∑' τ, euclNorm (condCrossG P φ g i₀ τ m - statCrossG P π φ g m) ≤
      C₂ * (1 + euclNorm (σ i₀) ^ q₂)

/-- Assumption 4: the (predetermined) step sizes are nonnegative and nonincreasing, with
`Σ γ_t = ∞` and `Σ γ_t² < ∞`. -/
structure Assumption4 (γ : ℕ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ γ t
  antitone : Antitone γ
  sum_diverges : Filter.Tendsto (fun n => ∑ t ∈ range n, γ t) Filter.atTop Filter.atTop
  sq_summable : Summable (fun t => γ t ^ 2)

end Assumptions

/-! ## The stationary process of §5 (p. 15) and the steady-state step -/

section Stationary

variable {S : Type*} [MeasurableSpace S] {K : ℕ}

/-- A two-sided Markov chain `(i_t)_{t ∈ ℤ}` on a probability space `(Ω, μ)` with transition
kernel `P`, already in steady state with law `π`: for every start `a`, length `n` and states
`s_0, …, s_n`, `Pr(i_a = s_0, …, i_{a+n} = s_n) = π(s_0) p_{s_0 s_1} ⋯ p_{s_{n−1} s_n}`. -/
structure IsStationaryChain {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (P : Kernel S S)
    (π : Measure S) (i : ℤ → Ω → S) : Prop where
  measurable : ∀ t, Measurable (i t)
  fdd : ∀ (a : ℤ) (n : ℕ) (s : Fin (n + 1) → S),
    μ {ω | ∀ k : Fin (n + 1), i (a + (k : ℕ)) ω = s k} =
      π {s 0} * ∏ k : Fin n, P (s k.castSucc) {s k.succ}

/-- The steady-state eligibility vector of Eq. (5): `z_t = Σ_{τ=−∞}^t (αλ)^{t−τ} φ(i_τ)`,
written `Σ_{τ ≥ 0} (αλ)^τ φ(i_{t−τ})`. -/
noncomputable def zStat {Ω : Type*} (α lam : ℝ) (φ : S → Fin K → ℝ) (i : ℤ → Ω → S) (t : ℤ)
    (ω : Ω) : Fin K → ℝ :=
  ∑' τ : ℕ, (α * lam) ^ τ • φ (i (t - τ) ω)

/-- The step `s(r, X) = (g(i, j) + αJ̃(j, r) − J̃(i, r)) z` for `X = (i, j, z)` (p. 7). -/
def sStep (α : ℝ) (g : S → S → ℝ) (φ : S → Fin K → ℝ) (r : Fin K → ℝ)
    (x : S × S × (Fin K → ℝ)) : Fin K → ℝ :=
  (g x.1 x.2.1 + α * (φ x.2.1 ⬝ᵥ r) - φ x.1 ⬝ᵥ r) • x.2.2

/-- The steady-state process `X_t = (i_t, i_{t+1}, z_t)` of §5. -/
noncomputable def Xstat {Ω : Type*} (α lam : ℝ) (φ : S → Fin K → ℝ) (i : ℤ → Ω → S) (t : ℤ)
    (ω : Ω) : S × S × (Fin K → ℝ) :=
  (i t ω, i (t + 1) ω, zStat α lam φ i t ω)

/-- `A(X) = z(αφ′(j) − φ′(i))` for `X = (i, j, z)` (§6, p. 18). -/
def Amat (α : ℝ) (φ : S → Fin K → ℝ) (x : S × S × (Fin K → ℝ)) : Matrix (Fin K) (Fin K) ℝ :=
  fun k l => x.2.2 k * (α * φ x.2.1 l - φ x.1 l)

/-- `b(X) = z g(i, j)` for `X = (i, j, z)` (§6, p. 19). -/
def bvec (g : S → S → ℝ) (x : S × S × (Fin K → ℝ)) : Fin K → ℝ :=
  fun k => x.2.2 k * g x.1 x.2.1

end Stationary

/-! ## The abstract stochastic approximation scheme of Theorem 2 (p. 18) -/

/-- The iterates `r_{t+1} = r_t + γ_t (A(X_t) r_t + b(X_t))` along a path `ω` of `X_t`. -/
def saIter {𝒳 : Type*} {K : ℕ} (γ : ℕ → ℝ) (A : 𝒳 → Matrix (Fin K) (Fin K) ℝ)
    (b : 𝒳 → Fin K → ℝ) (r₀ : Fin K → ℝ) (ω : ℕ → 𝒳) : ℕ → Fin K → ℝ
  | 0 => r₀
  | t + 1 => saIter γ A b r₀ ω t + γ t • (A (ω t) *ᵥ saIter γ A b r₀ ω t + b (ω t))

end TDApprox.Conv



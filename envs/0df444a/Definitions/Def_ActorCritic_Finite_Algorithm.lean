-- Prove2me | Definitions.Def_ActorCritic_Finite_Algorithm
-- name    : ActorCritic_Finite_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:30.73912+00:00
-- url     : https://prove2.me/theorems/d5dcf675-921f-4cac-b58b-810bf9fd6a81
-- title:
--   (3.1)–(3.2) — the actor–critic recursion with TD(1) or TD(λ) critic and the law of its simulated path
-- statement:
--   This module defines the two actor–critic algorithms of §3 and the probability law of their simulated path.
--
--   **Parameters.** At time $k$ the algorithm holds the actor parameter $\theta_k\in\mathbb R^n$, the critic parameter $r_k\in\mathbb R^m$, an estimate $\alpha_k\in\mathbb R$ of the average cost and an eligibility trace $\hat Z_k\in\mathbb R^m$. Given the current pair $(\hat X_k,\hat U_k)$ and the next pair $(\hat X_{k+1},\hat U_{k+1})$, with step sizes $\beta_k,\gamma_k$ and a scalar function $\Gamma$ on $\mathbb R^m$:
--   $$
--   d_k=c(\hat X_k,\hat U_k)-\alpha_k+r_k'\phi_{\theta_k}(\hat X_{k+1},\hat U_{k+1})-r_k'\phi_{\theta_k}(\hat X_k,\hat U_k),
--   $$
--   $$
--   \alpha_{k+1}=\alpha_k+\gamma_k\big(c(\hat X_{k+1},\hat U_{k+1})-\alpha_k\big),\qquad r_{k+1}=r_k+\gamma_kd_k\hat Z_k,
--   $$
--   $$
--   \theta_{k+1}=\theta_k-\beta_k\Gamma(r_k)\,r_k'\phi_{\theta_k}(\hat X_{k+1},\hat U_{k+1})\,\psi_{\theta_k}(\hat X_{k+1},\hat U_{k+1}),
--   $$
--   and the trace is updated by
--   1. **TD(1) critic:** $\hat Z_{k+1}=\hat Z_k+\phi_{\theta_k}(\hat X_{k+1},\hat U_{k+1})$ if $\hat X_{k+1}\ne x^*$, and $\hat Z_{k+1}=\phi_{\theta_k}(\hat X_{k+1},\hat U_{k+1})$ otherwise;
--   2. **TD($\lambda$) critic:** $\hat Z_{k+1}=\lambda\hat Z_k+\phi_{\theta_k}(\hat X_{k+1},\hat U_{k+1})$.
--
--   Starting from deterministic $(\theta_0,r_0,\alpha_0,\hat Z_0)$, the recursion turns a path $\omega=((\hat X_k,\hat U_k))_{k\ge0}$ into the sequence of parameters; the parameters at time $k$ depend on $(\hat X_0,\hat U_0),\dots,(\hat X_k,\hat U_k)$ only.
--
--   **Law of the simulated path.** $(\hat X_0,\hat U_0)$ has a given law $\nu_0$ on $\mathbb X\times\mathbb U$, and, given the history up to time $k$, the next state $\hat X_{k+1}$ is drawn from $p(\cdot\mid\hat X_k,\hat U_k)$ and the next action $\hat U_{k+1}$ from $\mu_{\theta_k}(\cdot\mid\hat X_{k+1})$, where $\theta_k$ is the actor parameter computed from that history. The law of the whole path on $(\mathbb X\times\mathbb U)^{\mathbb N}$ is the Ionescu-Tulcea measure of these transitions.
--
--   This is the algorithm whose convergence Theorem 3.4 asserts.
--
--   **Formalization Note** The $\alpha$-update uses $c(\hat X_{k+1},\hat U_{k+1})$ as printed in (3.1); the rewriting on p. 1156 uses $c(\hat X_k,\hat U_k)$, which does not change the limit. The transition kernel at time $k$ evaluates $\theta_k$ on the finite history extended to a path by repeating its last entry; only entries $0,\dots,k$ are read. $\mathbb X$ and $\mathbb U$ carry σ-algebras in which singletons are measurable (the discrete σ-algebra, as they are finite). The path law is Mathlib's `Kernel.trajMeasure`; its kernels are probability kernels, which is proved in the module.
-- source:
--   Konda and Tsitsiklis, On Actor-Critic Algorithms, SIAM J. Control Optim. 42 (2003), p. 1148, (3.1), (3.2), TD(1) and TD(λ) critics

import Mathlib
import Definitions.Def_ActorCritic_Finite_Model

namespace ActorCritic.Finite

open MeasureTheory ProbabilityTheory

/-- The two critics of §3 (p. 1148): the TD(1) critic, whose eligibility trace is reset when the
state `x*` is entered, and the TD(λ) critic with trace-decay parameter `λ` (used with
`0 < λ < 1`). -/
inductive Critic (X : Type) where
  /-- TD(1) critic, resetting at the state `xstar` -/
  | td1 (xstar : X) : Critic X
  /-- TD(λ) critic with parameter `lam` -/
  | tdLambda (lam : ℝ) : Critic X

/-- The parameters carried by the algorithm at time `k`: actor parameter `θ_k ∈ ℝⁿ`, critic
parameter `r_k ∈ ℝ^m`, average-cost estimate `α_k ∈ ℝ` and eligibility trace `Ẑ_k ∈ ℝ^m`. -/
structure ACState (n m : ℕ) where
  θ : EuclideanSpace ℝ (Fin n)
  r : EuclideanSpace ℝ (Fin m)
  α : ℝ
  Z : EuclideanSpace ℝ (Fin m)

variable {X U : Type} [Fintype X] [Fintype U] [DecidableEq X] {n m : ℕ}

/-- One step of the actor–critic recursion (3.1)–(3.2) (p. 1148), from the parameters `s` at
time `k`, the current pair `w = (X̂_k, Û_k)` and the next pair `w' = (X̂_{k+1}, Û_{k+1})`:
* `d_k = c(X̂_k, Û_k) − α_k + r_k' φ_{θ_k}(X̂_{k+1}, Û_{k+1}) − r_k' φ_{θ_k}(X̂_k, Û_k)`;
* `α_{k+1} = α_k + γ_k (c(X̂_{k+1}, Û_{k+1}) − α_k)` (as printed in (3.1));
* `r_{k+1} = r_k + γ_k d_k Ẑ_k`;
* `θ_{k+1} = θ_k − β_k Γ(r_k) r_k' φ_{θ_k}(X̂_{k+1}, Û_{k+1}) ψ_{θ_k}(X̂_{k+1}, Û_{k+1})`;
* TD(1): `Ẑ_{k+1} = Ẑ_k + φ_{θ_k}(X̂_{k+1}, Û_{k+1})` if `X̂_{k+1} ≠ x*`, and
  `Ẑ_{k+1} = φ_{θ_k}(X̂_{k+1}, Û_{k+1})` otherwise;
  TD(λ): `Ẑ_{k+1} = λ Ẑ_k + φ_{θ_k}(X̂_{k+1}, Û_{k+1})`. -/
noncomputable def acStep (M : FiniteMDP X U) (π : RSPFamily X U n)
    (φ : EuclideanSpace ℝ (Fin n) → X → U → EuclideanSpace ℝ (Fin m))
    (β γ : ℕ → ℝ) (Γ : EuclideanSpace ℝ (Fin m) → ℝ) (crit : Critic X)
    (k : ℕ) (s : ACState n m) (w w' : X × U) : ACState n m :=
  let φw := φ s.θ w.1 w.2
  let φw' := φ s.θ w'.1 w'.2
  let d := M.c w.1 w.2 - s.α + inner ℝ s.r φw' - inner ℝ s.r φw
  { α := s.α + γ k * (M.c w'.1 w'.2 - s.α)
    r := s.r + (γ k * d) • s.Z
    θ := s.θ - (β k * Γ s.r * inner ℝ s.r φw') • score π s.θ w'.1 w'.2
    Z := match crit with
      | Critic.td1 xstar => if w'.1 ≠ xstar then s.Z + φw' else φw'
      | Critic.tdLambda lam => lam • s.Z + φw' }

/-- The parameters `(θ_k, r_k, α_k, Ẑ_k)` produced by the recursion (3.1)–(3.2) along a path
`ω : ℕ → X × U` of simulated state–action pairs `ω k = (X̂_k, Û_k)`, from the deterministic
initial values `s₀ = (θ_0, r_0, α_0, Ẑ_0)`. The value at time `k` depends on `ω 0, …, ω k` only. -/
noncomputable def acIter (M : FiniteMDP X U) (π : RSPFamily X U n)
    (φ : EuclideanSpace ℝ (Fin n) → X → U → EuclideanSpace ℝ (Fin m))
    (β γ : ℕ → ℝ) (Γ : EuclideanSpace ℝ (Fin m) → ℝ) (crit : Critic X)
    (s₀ : ACState n m) (ω : ℕ → X × U) : ℕ → ACState n m
  | 0 => s₀
  | k + 1 => acStep M π φ β γ Γ crit k (acIter M π φ β γ Γ crit s₀ ω k) (ω k) (ω (k + 1))

/-- Extend a finite history `(w_0, …, w_k)` to a path by repeating its last entry `w_k`.
Only the entries `0, …, k` are ever read by `acIter … k`. -/
def extendHistory {W : Type} (k : ℕ) (h : (i : Finset.Iic k) → W) : ℕ → W :=
  fun i => if hi : i ≤ k then h ⟨i, Finset.mem_Iic.2 hi⟩ else h ⟨k, Finset.mem_Iic.2 le_rfl⟩

/-- The law of the next simulated pair given the current pair `w = (x, u)` and actor parameter
`θ`: the next state `y` has law `p(· | x, u)` and the next action `ū` has law `μ_θ(· | y)`,
i.e. `(y, ū)` has probability `p(y | x, u) μ_θ(ū | y)` (p. 1148). -/
noncomputable def nextLaw [MeasurableSpace X] [MeasurableSpace U]
    (M : FiniteMDP X U) (π : RSPFamily X U n) (θ : EuclideanSpace ℝ (Fin n)) (w : X × U) :
    Measure (X × U) :=
  ∑ y : X, ∑ v : U, ENNReal.ofReal (M.p w.1 w.2 y * π.μ θ y v) • Measure.dirac (y, v)

/-- The transition kernel of the simulated process at time `k`: given the history
`(X̂_0, Û_0, …, X̂_k, Û_k)`, the next pair `(X̂_{k+1}, Û_{k+1})` has law `nextLaw` evaluated at
`(X̂_k, Û_k)` and at the actor parameter `θ_k` that the recursion computes from that history
(p. 1148: "A new action `Û_{k+1}` is generated according to the RSP corresponding to the actor
parameter vector `θ_k`"). -/
noncomputable def acKernel [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (M : FiniteMDP X U) (π : RSPFamily X U n)
    (φ : EuclideanSpace ℝ (Fin n) → X → U → EuclideanSpace ℝ (Fin m))
    (β γ : ℕ → ℝ) (Γ : EuclideanSpace ℝ (Fin m) → ℝ) (crit : Critic X)
    (s₀ : ACState n m) (k : ℕ) :
    Kernel ((i : Finset.Iic k) → X × U) (X × U) :=
  Kernel.ofFunOfCountable fun h =>
    nextLaw M π (acIter M π φ β γ Γ crit s₀ (extendHistory k h) k).θ (h ⟨k, Finset.mem_Iic.2 le_rfl⟩)

instance isProbabilityMeasure_nextLaw [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (M : FiniteMDP X U) (π : RSPFamily X U n) (θ : EuclideanSpace ℝ (Fin n)) (w : X × U) :
    IsProbabilityMeasure (nextLaw M π θ w) := by
  constructor
  simp only [nextLaw, Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply,
    Pi.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_one]
  have hnn : ∀ y v, 0 ≤ M.p w.1 w.2 y * π.μ θ y v :=
    fun y v => mul_nonneg (M.p_nonneg _ _ _) (π.μ_nonneg _ _ _)
  have h1 : ∑ y, ∑ v, M.p w.1 w.2 y * π.μ θ y v = 1 := by
    simp_rw [← Finset.mul_sum, π.μ_sum_one, mul_one, M.p_sum_one]
  rw [← h1, ENNReal.ofReal_sum_of_nonneg (fun y _ => Finset.sum_nonneg fun v _ => hnn y v)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun v _ => hnn y v)]

instance isMarkovKernel_acKernel [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (M : FiniteMDP X U) (π : RSPFamily X U n)
    (φ : EuclideanSpace ℝ (Fin n) → X → U → EuclideanSpace ℝ (Fin m))
    (β γ : ℕ → ℝ) (Γ : EuclideanSpace ℝ (Fin m) → ℝ) (crit : Critic X)
    (s₀ : ACState n m) (k : ℕ) :
    IsMarkovKernel (acKernel M π φ β γ Γ crit s₀ k) := by
  constructor
  intro h
  change IsProbabilityMeasure (nextLaw M π _ _)
  infer_instance

/-- The law of the simulated path `(X̂_k, Û_k)_{k ≥ 0}` of the actor–critic algorithm on
`ℕ → X × U` (Ionescu-Tulcea): `(X̂_0, Û_0)` has law `ν₀`, and the transition from time `k` to
`k + 1` is `acKernel … k`, which uses the actor parameter `θ_k` computed by the recursion
from the initial values `s₀` and the history. -/
noncomputable def pathLaw [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (M : FiniteMDP X U) (π : RSPFamily X U n)
    (φ : EuclideanSpace ℝ (Fin n) → X → U → EuclideanSpace ℝ (Fin m))
    (β γ : ℕ → ℝ) (Γ : EuclideanSpace ℝ (Fin m) → ℝ) (crit : Critic X)
    (s₀ : ACState n m) (ν₀ : Measure (X × U)) : Measure (ℕ → X × U) :=
  Kernel.trajMeasure (X := fun _ => X × U) ν₀ (acKernel M π φ β γ Γ crit s₀)

end ActorCritic.Finite



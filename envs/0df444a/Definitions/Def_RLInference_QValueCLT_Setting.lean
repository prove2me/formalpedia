-- Prove2me | Definitions.Def_RLInference_QValueCLT_Setting
-- name    : RLInference_QValueCLT_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:12:19.360048+00:00
-- url     : https://prove2.me/theorems/0413abb2-e525-4475-8064-368446d13092
-- title:
--   §2–§3, (1)–(6), (8), pp. 7–12 — finite MDP, Bellman fixed point, data chain under π, estimators (2)–(3), P̃^π, P̃^{π*}, Σ_{P_{s,a}}, Σ_{R,P}, Σ
-- statement:
--   The objects of Zhu, Dong and Lam's asymptotic theory for plug-in Q-value estimates in a finite Markov decision process (MDP).
--
--   **The MDP.** Let $\mathcal S$ and $\mathcal A$ be finite sets of states and actions, and write $x=(s,a)$ for a state-action pair. A transition law assigns to each pair a probability vector $P(\cdot\mid s,a)$ on $\mathcal S$; a reward law assigns to each pair a probability measure $R(s,a)$ on $\mathbb R$ with mean $\mu_R(s,a)=\int r\,R(s,a)(dr)$ and variance $\sigma^2_R(s,a)$. For a discount factor $\gamma$, a reward vector $r$ and a transition array $P'$ (any real array indexed by $(s,a)$ and $k\in\mathcal S$), the **Bellman operator** of (1) is
--
--   $$\mathcal T_{r,P'}(Q)(s,a)=r(s,a)+\gamma\sum_{k\in\mathcal S}P'(k\mid s,a)\max_{a'\in\mathcal A}Q(k,a').$$
--
--   Its fixed point $\operatorname{Fix}(\gamma,r,P')$ is defined as the limit of value iteration $\mathcal T_{r,P'}^m(0)$ as $m\to\infty$. For $0\le\gamma<1$ and stochastic $P'$ (indeed whenever $\gamma\max_x\sum_k|P'(k\mid x)|<1$) the operator is a sup-norm contraction, and this limit is its unique fixed point. The Q-values are $Q=\operatorname{Fix}(\gamma,\mu_R,P)$ and $V^*(s)=\max_a Q(s,a)$.
--
--   **Data.** Given an exploration policy $\pi(\cdot\mid s)$, the data form a Markov chain $((s_t,a_t),r_t)_{t\ge0}$ on $(\mathcal S\times\mathcal A)\times\mathbb R$. From the pair $(s_t,a_t)$, the next state is $s_{t+1}\sim P(\cdot\mid s_t,a_t)$, the next action is $a_{t+1}\sim\pi(\cdot\mid s_{t+1})$, and the next reward is $r_{t+1}\sim R(s_{t+1},a_{t+1})$, so each reward and the following state are conditionally independent given the current pair. The initial state is drawn from a probability vector $\nu_0$ on $\mathcal S$, with $a_0\sim\pi(\cdot\mid s_0)$ and $r_0\sim R(s_0,a_0)$. The path law is the published Markov chain path measure.
--
--   **Estimators** (2), (3). With $N_n(s,a)=\#\{t<n:(s_t,a_t)=(s,a)\}$, the sample mean is $\hat\mu_{R,n}(s,a)=N_n(s,a)^{-1}\sum_{t<n,\,(s_t,a_t)=(s,a)}r_t$ and the empirical transition matrix is $\hat P_n(k\mid s,a)=N_n(s,a)^{-1}\#\{t<n:(s_t,a_t)=(s,a),\,s_{t+1}=k\}$. At unvisited pairs ($N_n(s,a)=0$) they take the initial values $u^0(s,a)$ and $p^0(k\mid s,a)$. The plug-in estimate is $\hat Q_n=\operatorname{Fix}(\gamma,\hat\mu_{R,n},\hat P_n)$.
--
--   **Matrices.** The following are indexed by state-action pairs:
--   1. the extended transition matrix $\tilde P^\pi((s,a),(s',a'))=P(s'\mid s,a)\pi(a'\mid s')$;
--   2. for a greedy action map $a^*$, $\tilde P^{\pi^*}((s,a),(s',a'))=P(s'\mid s,a)\mathbb 1(a'=a^*(s'))$;
--   3. for any $Q'$, $\tilde P'((s,a),(k,l))=P'(k\mid s,a)\mathbb 1(Q'(k,l)=\max_u Q'(k,u))$.
--
--   The multinomial covariance (4) is $\Sigma_{P_{s,a}}(k_1,k_2)=P(k_1\mid s,a)(1-P(k_1\mid s,a))$ for $k_1=k_2$ and $-P(k_1\mid s,a)P(k_2\mid s,a)$ otherwise. With $W=\operatorname{diag}(w)$, $D_R=\operatorname{diag}(\sigma^2_R)$ and $D_Q=\operatorname{diag}\big((V^*)^T\Sigma_{P_{s,a}}V^*\big)$ as in (6), the covariance (5) is
--
--   $$\Sigma=(I-\gamma\tilde P^{\pi^*})^{-1}W^{-1}(D_R+\gamma^2D_Q)\big((I-\gamma\tilde P^{\pi^*})^{-1}\big)^T.$$
--
--   The covariance (8) of the parameter vector $[\mu_R,P]$ is $\Sigma_{R,P}=\operatorname{diag}(W^{-1}D_R,D_P)$, where $D_P$ is block diagonal with blocks $\Sigma_{P_{s,a}}/w(s,a)$. The gradient of App. A.1 is $\nabla\phi=(I-\gamma\tilde P^{\pi^*})^{-1}[\,I\mid\gamma\operatorname{blockdiag}((V^*)^T)\,]$.
--
--   These definitions are shared by every statement of the mission: Theorem 1 and the displayed steps of its proof.
--
--   **Formalization Note.** State-action pairs are indexed by $\mathcal S\times\mathcal A$, and transition entries by $(\mathcal S\times\mathcal A)\times\mathcal S$. The paper's flattening $(i-1)m_a+j$ and $(i-1)N+(j-1)m_s+k$ is notation only. Time is 0-based: the paper's observation $t=1,\dots,n$ is Lean's $t=0,\dots,n-1$, and $s'_t=s_{t+1}$. $P$, $\pi$ and $\nu_0$ are `PMF`s, and $P$ is read as the real array `Pmat P`. The data chain is a reading of "collected according to $\pi$"; the paper does not write the joint law. `bellmanFix` is a value-iteration limit (`limUnder`). It is only meaningful where that limit exists, which covers every stochastic $P'$ and a neighbourhood of $(\mu_R,P)$. The parameter vector $[\mu_R,P]$ is indexed by $(\mathcal S\times\mathcal A)\oplus((\mathcal S\times\mathcal A)\times\mathcal S)$. `Matrix.inv` returns $0$ on singular matrices. $I-\gamma\tilde P^{\pi^*}$ is invertible for $0\le\gamma<1$, so $\Sigma$ is the true matrix.
-- source:
--   Zhu, Dong & Lam, Uncertainty Quantification and Exploration for Reinforcement Learning, arXiv:1910.05471v3, pp. 7–12, §2–§3, (1)–(6), (8); App. A.1, pp. 34–36

import Mathlib
import Definitions.Def_MarkovChainPathMeasure

namespace RLInference.QValueCLT

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped ENNReal

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-! ### The MDP: transition matrix, reward moments, Bellman operator (pp. 7–8, (1)) -/

/-- The transition matrix `P(k | x)`, `x = (s,a)`, as a real `(S × A) × S` array. -/
noncomputable def Pmat (P : S × A → PMF S) : S × A → S → ℝ :=
  fun x k => (P x k).toReal

/-- The mean reward `μ_R(s,a) = E[R(s,a)]`. -/
noncomputable def muR (R : S × A → Measure ℝ) : S × A → ℝ :=
  fun x => ∫ r, r ∂(R x)

/-- The reward variance `σ²_R(s,a) = Var[R(s,a)]`. -/
noncomputable def sigma2R (R : S × A → Measure ℝ) : S × A → ℝ :=
  fun x => variance id (R x)

/-- The Bellman operator `𝒯_{r,P'}` of (1):
`𝒯_{r,P'}(Q)(s,a) = r(s,a) + γ ∑_k P'(k | s,a) max_{a'} Q(k,a')`. -/
noncomputable def bellman (γ : ℝ) (r : S × A → ℝ) (P' : S × A → S → ℝ)
    (Q : S × A → ℝ) : S × A → ℝ :=
  fun x => r x + γ * ∑ k, P' x k * ⨆ a, Q (k, a)

/-- The fixed point of `𝒯_{r,P'}`, as the limit of value iteration from `0`.
It is the unique fixed point whenever `γ · max_x ∑_k |P'(k | x)| < 1`, in particular
for every stochastic `P'` and `0 ≤ γ < 1`. -/
noncomputable def bellmanFix (γ : ℝ) (r : S × A → ℝ) (P' : S × A → S → ℝ) : S × A → ℝ :=
  limUnder atTop (fun m : ℕ => (bellman γ r P')^[m] 0)

/-- `V*(s) = max_a Q(s,a)`. -/
noncomputable def Vstar [Nonempty A] (Q : S × A → ℝ) : S → ℝ :=
  fun k => ⨆ a, Q (k, a)

/-! ### Extended chains and covariance matrices (pp. 8–12, (4)–(6), (8)) -/

/-- `P̃^π((s,a),(s',a')) = P(s' | s,a) π(a' | s')`, an `(S × A) × (S × A)` matrix. -/
noncomputable def Ptilde (P : S × A → PMF S) (π : S → PMF A) : Matrix (S × A) (S × A) ℝ :=
  fun x y => Pmat P x y.1 * (π y.1 y.2).toReal

/-- `P̃^{π*}((s,a),(s',a')) = P(s' | s,a) 1(a' = a*(s'))` for the greedy policy `a*`. -/
noncomputable def PtildeStar (P' : S × A → S → ℝ) (aStar : S → A) :
    Matrix (S × A) (S × A) ℝ :=
  fun x y => P' x y.1 * if y.2 = aStar y.1 then 1 else 0

/-- `P̃'((s,a),(k,l)) = P'(k | s,a) 1(Q'(k,l) = max_u Q'(k,u))` (App. A.1, p. 35). -/
noncomputable def PtildePrime [Nonempty A] (P' : S × A → S → ℝ) (Q' : S × A → ℝ) :
    Matrix (S × A) (S × A) ℝ :=
  fun x y => P' x y.1 * if Q' y = ⨆ u, Q' (y.1, u) then 1 else 0

/-- The multinomial sampling covariance `Σ_{P_{s,a}}` of (4). -/
noncomputable def SigmaP (P' : S × A → S → ℝ) (x : S × A) : Matrix S S ℝ :=
  fun k₁ k₂ => if k₁ = k₂ then P' x k₁ * (1 - P' x k₁) else -(P' x k₁ * P' x k₂)

/-- `D_Q = diag((V*)ᵀ Σ_{P_{s,a}} V*)` of (6). -/
noncomputable def DQ (P' : S × A → S → ℝ) (V : S → ℝ) : Matrix (S × A) (S × A) ℝ :=
  diagonal fun x => ∑ k₁, ∑ k₂, V k₁ * SigmaP P' x k₁ k₂ * V k₂

/-- The asymptotic covariance `Σ = (I − γP̃^{π*})⁻¹ W⁻¹ (D_R + γ² D_Q) ((I − γP̃^{π*})⁻¹)ᵀ`
of (5), with `W = diag(w)`, `D_R = diag(σ²_R)`. -/
noncomputable def SigmaQ (γ : ℝ) (P' : S × A → S → ℝ) (aStar : S → A) (V : S → ℝ)
    (sig2 w : S × A → ℝ) : Matrix (S × A) (S × A) ℝ :=
  (1 - γ • PtildeStar P' aStar)⁻¹ * diagonal (fun x => (w x)⁻¹) *
    (diagonal sig2 + γ ^ 2 • DQ P' V) * ((1 - γ • PtildeStar P' aStar)⁻¹)ᵀ

/-- The block `D_P` of (8): block diagonal, block `(s,a)` equal to `Σ_{P_{s,a}} / w(s,a)`. -/
noncomputable def DP (P' : S × A → S → ℝ) (w : S × A → ℝ) :
    Matrix ((S × A) × S) ((S × A) × S) ℝ :=
  fun p q => if p.1 = q.1 then SigmaP P' p.1 p.2 q.2 / w p.1 else 0

/-- `Σ_{R,P} = diag(W⁻¹ D_R, D_P)` of (8), indexed by `(S × A) ⊕ ((S × A) × S)`. -/
noncomputable def SigmaRP (P' : S × A → S → ℝ) (sig2 w : S × A → ℝ) :
    Matrix ((S × A) ⊕ ((S × A) × S)) ((S × A) ⊕ ((S × A) × S)) ℝ :=
  fromBlocks (diagonal fun x => sig2 x / w x) 0 0 (DP P' w)

/-- The block-diagonal matrix `blockdiag((V*)ᵀ, …, (V*)ᵀ)` (App. A.1, p. 36): row `x` carries
`(V*)ᵀ` in the columns `(x, k)`, `k ∈ S`, and zeros elsewhere. -/
def blockV (V : S → ℝ) : Matrix (S × A) ((S × A) × S) ℝ :=
  Matrix.of fun x q => if x = q.1 then V q.2 else 0

/-- The gradient `∇φ(μ_R, P) = (I − γP̃^{π*})⁻¹ [I | γ blockdiag((V*)ᵀ)]` (App. A.1, p. 36),
an `(S × A) × ((S × A) ⊕ ((S × A) × S))` matrix. -/
noncomputable def gradPhi (γ : ℝ) (P' : S × A → S → ℝ) (aStar : S → A) (V : S → ℝ) :
    Matrix (S × A) ((S × A) ⊕ ((S × A) × S)) ℝ :=
  (1 - γ • PtildeStar P' aStar)⁻¹ * fromCols (1 : Matrix (S × A) (S × A) ℝ) (γ • blockV V)

/-! ### The data: a Markov chain on `(S × A) × ℝ` under the exploration policy `π` -/

variable [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A]

/-- One step of data collection from the state-action pair `x = (s,a)`:
`s' ∼ P(· | s,a)`, `a' ∼ π(· | s')`, and the reward `r' ∼ R(s',a')` of the new pair. -/
noncomputable def dataStep (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    (x : S × A) : Measure ((S × A) × ℝ) :=
  ∑ y : S × A, (P x y.1 * π y.1 y.2) • (Measure.dirac y).prod (R y)

/-- The transition kernel of the data chain `((s_t,a_t), r_t)`; it ignores the reward. -/
noncomputable def dataKernel (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ) :
    Kernel ((S × A) × ℝ) ((S × A) × ℝ) where
  toFun z := dataStep P π R z.1
  measurable' := (measurable_of_finite (dataStep P π R)).comp measurable_fst

/-- The law of the first observation: `s₁ ∼ ν₀`, `a₁ ∼ π(· | s₁)`, `r₁ ∼ R(s₁,a₁)`. -/
noncomputable def initLaw (ν₀ : PMF S) (π : S → PMF A) (R : S × A → Measure ℝ) :
    Measure ((S × A) × ℝ) :=
  ∑ y : S × A, (ν₀ y.1 * π y.1 y.2) • (Measure.dirac y).prod (R y)

omit [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma sum_pmf_mul_pmf (ν : PMF S) (π : S → PMF A) :
    ∑ y : S × A, ν y.1 * π y.1 y.2 = 1 := by
  have h : ∀ μ : PMF A, ∑ a, μ a = 1 := fun μ => (tsum_fintype _).symm.trans μ.tsum_coe
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, h, mul_one]
  exact (tsum_fintype _).symm.trans ν.tsum_coe

omit [DecidableEq S] [DecidableEq A] [MeasurableSingletonClass S]
  [MeasurableSingletonClass A] in
lemma mixture_univ (c : S × A → ℝ≥0∞) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] :
    (∑ y : S × A, c y • (Measure.dirac y).prod (R y)) Set.univ = ∑ y, c y := by
  simp [Finset.sum_apply]

instance dataKernel.instIsMarkovKernel (P : S × A → PMF S) (π : S → PMF A)
    (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)] :
    IsMarkovKernel (dataKernel P π R) :=
  ⟨fun z => ⟨by
    change (dataStep P π R z.1) Set.univ = 1
    rw [dataStep, mixture_univ, sum_pmf_mul_pmf]⟩⟩

instance initLaw.instIsProbabilityMeasure (ν₀ : PMF S) (π : S → PMF A)
    (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)] :
    IsProbabilityMeasure (initLaw ν₀ π R) :=
  ⟨by rw [initLaw, mixture_univ, sum_pmf_mul_pmf]⟩

/-! ### Estimators (2), (3) and `Q̂_n` (p. 8). Time is 0-based: observation `t < n` is
`ω t = ((s_t, a_t), r_t)` and `s'_t = s_{t+1}` is `(ω (t+1)).1.1`. -/

/-- Number of visits to the pair `x` among the first `n` observations. -/
def visits (n : ℕ) (ω : ℕ → (S × A) × ℝ) (x : S × A) : ℕ :=
  ((Finset.range n).filter fun t => (ω t).1 = x).card

/-- The sample mean reward `μ̂_{R,n}` of (2), with fallback `u⁰` at unvisited pairs. -/
noncomputable def muHat (u0 : S × A → ℝ) (n : ℕ) (ω : ℕ → (S × A) × ℝ) : S × A → ℝ :=
  fun x => if 0 < visits n ω x then
      (∑ t ∈ (Finset.range n).filter (fun t => (ω t).1 = x), (ω t).2) / (visits n ω x : ℝ)
    else u0 x

/-- The empirical transition matrix `P̂_n` of (3), with fallback `p⁰` at unvisited pairs. -/
noncomputable def PHat (p0 : S × A → S → ℝ) (n : ℕ) (ω : ℕ → (S × A) × ℝ) :
    S × A → S → ℝ :=
  fun x k => if 0 < visits n ω x then
      (((Finset.range n).filter fun t => (ω t).1 = x ∧ (ω (t + 1)).1.1 = k).card : ℝ) /
        (visits n ω x : ℝ)
    else p0 x k

/-- The plug-in estimate `Q̂_n = 𝒯_{μ̂_{R,n}, P̂_n}(Q̂_n)`. -/
noncomputable def QHat (γ : ℝ) (u0 : S × A → ℝ) (p0 : S × A → S → ℝ) (n : ℕ)
    (ω : ℕ → (S × A) × ℝ) : S × A → ℝ :=
  bellmanFix γ (muHat u0 n ω) (PHat p0 n ω)

/-- The plug-in parameter vector `[μ̂_{R,n}, P̂_n]`, indexed by `(S × A) ⊕ ((S × A) × S)`. -/
noncomputable def thetaHat (u0 : S × A → ℝ) (p0 : S × A → S → ℝ) (n : ℕ)
    (ω : ℕ → (S × A) × ℝ) : (S × A) ⊕ ((S × A) × S) → ℝ :=
  Sum.elim (muHat u0 n ω) (fun q => PHat p0 n ω q.1 q.2)

/-- The true parameter vector `[μ_R, P]`. -/
noncomputable def theta (R : S × A → Measure ℝ) (P : S × A → PMF S) :
    (S × A) ⊕ ((S × A) × S) → ℝ :=
  Sum.elim (muR R) (fun q => Pmat P q.1 q.2)

end RLInference.QValueCLT



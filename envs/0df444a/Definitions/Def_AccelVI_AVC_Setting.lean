-- Prove2me | Definitions.Def_AccelVI_AVC_Setting
-- name    : AccelVI_AVC_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:27.841917+00:00
-- url     : https://prove2.me/theorems/c4c57947-05ee-424a-8b2c-e2e65eb17823
-- title:
--   §2, (2.4), Definition 2.1, (4.1), (A-VC), (5.1) — finite MDP, policy operator T_π, v^π, reversibility, κ, Accelerated Value Computation, the matrix B_π
-- statement:
--   This module fixes the objects of §2 and §5.1 of Goyal and Grand-Clément.
--
--   1. **MDP data.** A finite set of states $\mathbb S$ ($|\mathbb S| = n$), a finite set of actions $\mathbb A$, a transition kernel $P_{iaj}$ (the probability of moving from state $i$ to state $j$ under action $a$), a reward $r_{ia}\in\mathbb R$ for every state–action pair, and a discount factor $\lambda$. The data are **valid** when every $P_{ia\cdot}$ is a probability distribution over $\mathbb S$ and $\lambda\in(0,1)$. Rewards are arbitrary real numbers.
--   2. **Policies.** A (stationary, Markovian, possibly randomized) policy is $\pi\in\mathbb R_+^{n\times A}$ whose row $\pi_{i\cdot}$ is a probability distribution over $\mathbb A$ for every state $i$.
--   3. **Policy quantities.** The reward vector $r_{\pi,i}=\sum_{a}\pi_{ia}r_{ia}$, the transition matrix $L_{\pi,ij}=\sum_a\pi_{ia}P_{iaj}$, the affine policy operator (2.4)
--   $$T_\pi(v)=r_\pi+\lambda L_\pi v,$$
--   and the value function of $\pi$,
--   $$v^\pi=\sum_{t=0}^{\infty}\lambda^t L_\pi^{t}\,r_\pi,$$
--   which is the expected discounted reward $v^\pi_i=E^{\pi,P}\big[\sum_t\lambda^t r_{i_ta_t}\mid i_0=i\big]$ written in matrix form.
--   4. **Reversibility** (Definition 2.1). A transition matrix $L$ is reversible when it is irreducible (every state reaches every other state with positive probability in some number of steps) and has a stationary probability distribution $\nu$ satisfying the detailed balance equations $\nu_iL_{ij}=\nu_jL_{ji}$ for all $i,j$.
--   5. **Accelerated Value Computation** (A-VC). For step sizes $\alpha,\gamma$ and arbitrary $v_0,v_1\in\mathbb R^n$,
--   $$h_s=v_s+\gamma(v_s-v_{s-1}),\qquad v_{s+1}=h_s-\alpha\big(h_s-T_\pi(h_s)\big),\qquad s\ge 1.$$
--   The step sizes (4.1) are $\alpha=1/(1+\lambda)$ and $\gamma=\big(1-\sqrt{1-\lambda^2}\big)/\lambda$.
--   6. **Constants.** $\kappa=(1+\lambda)/(1-\lambda)$ and the rate $\theta=1-\sqrt{1/\kappa}$.
--   7. **The matrix (5.1).** With $I$ the $n\times n$ identity,
--   $$B_\pi=\begin{bmatrix}\big(1-\sqrt{1/\kappa}\big)(I+L_\pi) & -\tfrac12\big(1-\sqrt{1/\kappa}\big)^2(I+L_\pi)\\ I & 0\end{bmatrix}\in\mathbb R^{2n\times 2n},$$
--   together with the stacked vectors $x_s=(v_s,v_{s-1})$ (for $s\ge1$) and $x^\pi=(v^\pi,v^\pi)$ of Lemma 5.2.
--
--   These are the objects in which Theorem 5.1 and its lemmas are stated.
--
--   **Formalization Note.** The discount is `lam`, the policy `pol`; the initial-state distribution $p_0$ of the paper's tuple is omitted because no result here uses it. The general MDP vocabulary is the published `FoundationsML.ReinforcementLearning` layer: the kernel condition is `IsTransitionKernel`, a policy is `IsPolicy`, $r_\pi$ is `InducedReward`, $L_\pi$ is `InducedTransition` (wrapped as a matrix), and $v^\pi$ is `PolicyValue`, the discounted series $\sum_t\lambda^t\,E[r_{i_ta_t}\mid i_0=i]$ computed from the time-$t$ state distribution; it is the series above, not "some fixed point of $T_\pi$". Validity of the data and of the policy are hypotheses of every theorem. Irreducibility, stationarity (which includes being a probability vector) and detailed balance come from the published `mm_basic` vocabulary; detailed balance alone is not used as reversibility, since it holds for $\nu=0$. A-VC is a sequence indexed by $\mathbb N$ with $v_0,v_1$ given and the recursion at $s+2$. $x_s$ uses $v_{s-1}$, which for $s=0$ would be $v_0$ by truncated subtraction; it is only used for $s\ge1$. $B_\pi$ is a block matrix indexed by $\mathbb S\sqcup\mathbb S$.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, pp. 3–4, 6–8, §2, (2.4), Definition 2.1, (4.1), (A-VC), (5.1), Lemma 5.2

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue

namespace AccelVI.AVC

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- §2, p. 3: the data (P, r, λ) of an MDP (S, A, P, r, p₀, λ); p₀ is omitted (no planned result uses it). -/
structure MDP (S A : Type*) where
  P : S → A → S → ℝ
  r : S → A → ℝ
  lam : ℝ

/-- §2: every P_ia is a probability distribution over next states (the published
`IsTransitionKernel`), and λ ∈ (0, 1). -/
def MDP.Valid (M : MDP S A) : Prop :=
  FoundationsML.ReinforcementLearning.IsTransitionKernel M.P ∧ 0 < M.lam ∧ M.lam < 1

/-- r_π,i = Σ_a π_ia r_ia (the published `InducedReward`). A policy π ∈ ℝ₊^{n×A} (§2) is the
published predicate `FoundationsML.ReinforcementLearning.IsPolicy`. -/
noncomputable def rPol (M : MDP S A) (pol : S → A → ℝ) : S → ℝ :=
  FoundationsML.ReinforcementLearning.InducedReward pol M.r

/-- L_π,ij = Σ_a π_ia P_iaj (the published `InducedTransition`), as an n × n matrix. -/
noncomputable def LPol (M : MDP S A) (pol : S → A → ℝ) : Matrix S S ℝ :=
  Matrix.of (FoundationsML.ReinforcementLearning.InducedTransition pol M.P)

/-- (2.4): T_π(v) = r_π + λ L_π v. -/
noncomputable def Tpol (M : MDP S A) (pol : S → A → ℝ) (v : S → ℝ) : S → ℝ :=
  rPol M pol + M.lam • (LPol M pol).mulVec v

/-- §2: v^π_i = E^{π,P}[Σ_t λ^t r_{i_t a_t} | i_0 = i] (the published `PolicyValue`, the
discounted series of expected rewards Σ_t λ^t (L_π^t r_π)_i). -/
noncomputable def valuePol (M : MDP S A) (pol : S → A → ℝ) : S → ℝ :=
  FoundationsML.ReinforcementLearning.PolicyValue pol M.P M.r M.lam

/-- κ = (1 + λ)/(1 − λ) (Theorem 5.1). -/
noncomputable def kappa (lam : ℝ) : ℝ := (1 + lam) / (1 - lam)

/-- Definition 2.1, p. 4: the chain with transition matrix `L` is irreducible and admits a
stationary distribution `ν` satisfying the detailed balance equations `ν_i L_ij = ν_j L_ji`
(the stationary distribution is unique by irreducibility). -/
def IsReversible (L : Matrix S S ℝ) : Prop :=
  MarkovMixing.Irreducible L ∧
    ∃ ν : S → ℝ, MarkovMixing.IsStationary L ν ∧ MarkovMixing.DetailedBalance L ν

/-- Algorithm (A-VC), p. 7, with constant step sizes `α`, `γ`: `v₀, v₁` arbitrary and, for
`s ≥ 1`, `h_s = v_s + γ (v_s − v_{s−1})`, `v_{s+1} = h_s − α (h_s − T_π(h_s))`. -/
noncomputable def avc (M : MDP S A) (pol : S → A → ℝ) (α γ : ℝ) (v0 v1 : S → ℝ) : ℕ → (S → ℝ)
  | 0 => v0
  | 1 => v1
  | s + 2 =>
      let h := avc M pol α γ v0 v1 (s + 1) + γ • (avc M pol α γ v0 v1 (s + 1) - avc M pol α γ v0 v1 s)
      h - α • (h - Tpol M pol h)

/-- (4.1), p. 7: α = 1/(1 + λ). -/
noncomputable def alphaAVC (lam : ℝ) : ℝ := 1 / (1 + lam)

/-- (4.1), p. 7: γ = (1 − √(1 − λ²))/λ. -/
noncomputable def gammaAVC (lam : ℝ) : ℝ := (1 - Real.sqrt (1 - lam ^ 2)) / lam

/-- The rate 1 − √(1/κ) of Theorem 5.1 and Lemma 5.3. -/
noncomputable def theta (lam : ℝ) : ℝ := 1 - Real.sqrt (1 / kappa lam)

/-- (5.1), p. 8: the 2n × 2n matrix
`B_π = [[(1 − √(1/κ))(I + L_π), −(1 − √(1/κ))²/2 (I + L_π)], [I, 0]]`. -/
noncomputable def Bpol (M : MDP S A) (pol : S → A → ℝ) : Matrix (S ⊕ S) (S ⊕ S) ℝ :=
  Matrix.fromBlocks (theta M.lam • (1 + LPol M pol)) (-(theta M.lam ^ 2 / 2) • (1 + LPol M pol)) 1 0

/-- Lemma 5.2, p. 8: the stacked vector `x_s = (v_s, v_{s−1}) ∈ ℝ^{2n}` (used for `s ≥ 1`). -/
def xvec (v : ℕ → S → ℝ) (s : ℕ) : S ⊕ S → ℝ := Sum.elim (v s) (v (s - 1))

/-- Lemma 5.2, p. 8: `x^π = (v^π, v^π) ∈ ℝ^{2n}`. -/
noncomputable def xPi (M : MDP S A) (pol : S → A → ℝ) : S ⊕ S → ℝ :=
  Sum.elim (valuePol M pol) (valuePol M pol)

end AccelVI.AVC



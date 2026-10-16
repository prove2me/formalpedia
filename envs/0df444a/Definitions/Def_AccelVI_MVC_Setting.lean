-- Prove2me | Definitions.Def_AccelVI_MVC_Setting
-- name    : AccelVI_MVC_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:49.30903+00:00
-- url     : https://prove2.me/theorems/14bd7aff-cf98-4e7d-a6f0-1a0265601066
-- title:
--   §2, (2.4), Definition 2.1, (4.2), (M-VC), App. B — finite MDP, T_π, v^π, κ, reversibility, Momentum Value Computation, the matrix B_π
-- statement:
--   This file fixes the objects of the analysis of Momentum Value Computation by Goyal and Grand-Clément.
--
--   1. **MDP.** A finite Markov decision process has a finite state set $S$ ($|S| = n$), a finite action set $A$, transition probabilities $P_{iaj}$ (from state $i$ to state $j$ under action $a$), rewards $r_{ia} \in \mathbb{R}$ and a discount factor $\lambda$. It is **valid** when every $P_{ia} = (P_{iaj})_{j}$ is a probability vector and $0 < \lambda < 1$. The initial distribution $p_0$ of the paper is omitted, since no result here uses it.
--
--   2. **Policies.** A (stationary, possibly randomized) policy is a matrix $\pi = (\pi_{ia})$ with nonnegative entries and rows summing to $1$. It induces the reward vector $r_{\pi,i} = \sum_a \pi_{ia} r_{ia}$, the transition matrix $L_{\pi,ij} = \sum_a \pi_{ia} P_{iaj}$, the affine operator (2.4)
--   $$T_\pi(v) = r_\pi + \lambda L_\pi v, \qquad v \in \mathbb{R}^n,$$
--   and the value function $v^\pi = \sum_{t \ge 0} \lambda^t L_\pi^t r_\pi$, the expected discounted reward started from each state.
--
--   3. **Reversibility** (Definition 2.1). A transition matrix $L$ defines an irreducible, reversible Markov chain when the chain is irreducible (every state reaches every other with positive probability in some number of steps) and there is a stationary probability distribution $\nu$ satisfying the detailed balance equations $\nu_i L_{ij} = \nu_j L_{ji}$ for all $i, j$.
--
--   4. **Constants.** $\kappa = (1+\lambda)/(1-\lambda)$, the step sizes (4.2)
--   $$\alpha = \frac{2}{1 + \sqrt{1-\lambda^2}}, \qquad \beta = \frac{1 - \sqrt{1-\lambda^2}}{1 + \sqrt{1-\lambda^2}},$$
--   and the rate $\dfrac{1 - \sqrt{1/\kappa}}{1 + \sqrt{1/\kappa}}$ of Theorem 5.5.
--
--   5. **Momentum Value Computation** (M-VC): given $v_0, v_1 \in \mathbb{R}^n$ and constant step sizes $\alpha, \beta$,
--   $$v_{s+1} = v_s - \alpha\,(v_s - T_\pi(v_s)) + \beta\,(v_s - v_{s-1}), \qquad s \ge 1.$$
--
--   6. **The matrix of App. B.**
--   $$B_\pi = \begin{pmatrix} \lambda(\beta+1) L_\pi & -\beta I \\ I & 0 \end{pmatrix} \in \mathbb{R}^{2n \times 2n},$$
--   with $\beta$ as in (4.2); it propagates the error of the pair $x_s = (v_s, v_{s-1})$.
--
--   These are the objects in terms of which Lemmas B.1, B.2 and Theorem 5.5 are stated.
--
--   **Formalization Note.** The MDP data is a plain structure and validity the separate predicate `MDP.Valid`. The discount $\lambda$ is `lam` and the policy is `pol`. The value function is the Neumann series $\sum_t \lambda^t L_\pi^t r_\pi$ (a `tsum`), which is the paper's expectation written in matrix form. Reversibility uses the published `mm_basic` notions `Irreducible`, `IsStationary` (which includes that $\nu$ is a probability vector) and `DetailedBalance`. Display (4.2) prints the second step size as "$\gamma_s = \gamma$"; (M-VC) and App. B call it $\beta$, and so does the Lean (`betaMVC`). The iteration `mvc` is indexed so that `mvc … 0` $= v_0$, `mvc … 1` $= v_1$ and `mvc … (s+2)` is the (M-VC) step from $v_{s+1}, v_s$. $B_\pi$ is a block matrix indexed by $S \oplus S$, the first copy holding $v_s$ and the second $v_{s-1}$.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, pp. 3–4, 7, 8, 10, 21: §2, (2.4), Definition 2.1, (4.2), (M-VC), κ of Theorem 5.1, rate of Theorem 5.5, B_π of App. B

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting

namespace AccelVI.MVC

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- §2, p. 3: the data (P, r, λ) of an MDP (S, A, P, r, p₀, λ); p₀ is omitted (no planned result uses it). -/
structure MDP (S A : Type*) where
  P : S → A → S → ℝ
  r : S → A → ℝ
  lam : ℝ

/-- §2: P_ia is a probability distribution over next states, and λ ∈ (0, 1). -/
def MDP.Valid (M : MDP S A) : Prop :=
  (∀ i a j, 0 ≤ M.P i a j) ∧ (∀ i a, ∑ j, M.P i a j = 1) ∧ 0 < M.lam ∧ M.lam < 1

/-- §2: a stationary Markovian (possibly randomized) policy π ∈ ℝ₊^{n×A}. -/
def IsPolicy (pol : S → A → ℝ) : Prop := ∀ i, (∀ a, 0 ≤ pol i a) ∧ ∑ a, pol i a = 1

/-- r_π,i = Σ_a π_ia r_ia. -/
def rPol (M : MDP S A) (pol : S → A → ℝ) : S → ℝ := fun i => ∑ a, pol i a * M.r i a

/-- L_π,ij = Σ_a π_ia P_iaj. -/
def LPol (M : MDP S A) (pol : S → A → ℝ) : Matrix S S ℝ := fun i j => ∑ a, pol i a * M.P i a j

/-- (2.4): T_π(v) = r_π + λ L_π v. -/
def Tpol (M : MDP S A) (pol : S → A → ℝ) (v : S → ℝ) : S → ℝ :=
  rPol M pol + M.lam • (LPol M pol).mulVec v

/-- §2: v^π_i = E^{π,P}[Σ_t λ^t r_{i_t a_t} | i_0 = i] = Σ_t λ^t (L_π^t r_π)_i. -/
noncomputable def valuePol (M : MDP S A) (pol : S → A → ℝ) : S → ℝ :=
  ∑' t : ℕ, M.lam ^ t • ((LPol M pol) ^ t).mulVec (rPol M pol)

/-- (M-VC), p. 7: v₀, v₁ ∈ ℝⁿ, v_{s+1} = v_s − α (v_s − T_π(v_s)) + β (v_s − v_{s−1}) for s ≥ 1,
with constant step sizes α, β. -/
noncomputable def mvc (M : MDP S A) (pol : S → A → ℝ) (α β : ℝ) (v0 v1 : S → ℝ) : ℕ → (S → ℝ)
  | 0 => v0
  | 1 => v1
  | s + 2 => mvc M pol α β v0 v1 (s + 1) - α • (mvc M pol α β v0 v1 (s + 1) - Tpol M pol (mvc M pol α β v0 v1 (s + 1)))
             + β • (mvc M pol α β v0 v1 (s + 1) - mvc M pol α β v0 v1 s)

/-- (4.2), p. 7: α = 2/(1 + √(1 − λ²)). -/
noncomputable def alphaMVC (lam : ℝ) : ℝ := 2 / (1 + Real.sqrt (1 - lam ^ 2))

/-- (4.2), p. 7: the momentum coefficient β = (1 − √(1 − λ²))/(1 + √(1 − λ²)) (printed "γ" in (4.2);
called β in (M-VC) and App. B). -/
noncomputable def betaMVC (lam : ℝ) : ℝ := (1 - Real.sqrt (1 - lam ^ 2)) / (1 + Real.sqrt (1 - lam ^ 2))

/-- Theorem 5.5, p. 10: the rate (1 − √(1/κ))/(1 + √(1/κ)). -/
noncomputable def rateMVC (lam : ℝ) : ℝ := (1 - Real.sqrt (1 / AccelVI.AVC.kappa lam)) / (1 + Real.sqrt (1 / AccelVI.AVC.kappa lam))

/-- App. B, p. 21: B_π = [[λ(β + 1) L_π, −β I], [I, 0]] ∈ ℝ^{2n×2n}, with β of (4.2). -/
noncomputable def Bpol (M : MDP S A) (pol : S → A → ℝ) : Matrix (S ⊕ S) (S ⊕ S) ℝ :=
  Matrix.fromBlocks ((M.lam * (betaMVC M.lam + 1)) • LPol M pol) (-(betaMVC M.lam) • (1 : Matrix S S ℝ)) 1 0

end AccelVI.MVC



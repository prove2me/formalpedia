-- Prove2me | Definitions.Def_FiniteMemQL_Convergence_Setting
-- name    : FiniteMemQL_Convergence_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:05.288299+00:00
-- url     : https://prove2.me/theorems/1aeb33a9-7ad4-4f10-9967-ad6e14639011
-- title:
--   §3.1–3.2, (3.1)–(3.9) — window posteriors ψ, finite-window belief MDP, the approximate model at π*, its values, and the filter-stability term L_t
-- statement:
--   This module builds the finite-window belief MDP of §3.1, its approximation of §3.2, the fixed point $Q^*$ of (4.5) and the filter-stability term $L_t$ of (3.9).
--
--   **Windows.** A window $I=(y_{t-N},\dots,y_t;\,u_{t-N},\dots,u_{t-1})\in\mathbb Y^{N+1}\times\mathbb U^N$ holds the last $N+1$ observations and $N$ actions. For a prior $\pi$ on $X_{t-N}$, $\psi(\pi,I)=P^{\pi}(X_t\in\cdot\mid I)$ is the Bayesian update of $\pi$ along the window (Definition 3.1, p. 8). The finite-window state is $\hat z=(\pi,I)$. The module defines
--
--   1. the stage cost $\hat c(\pi,I,u)=\int c(x,u)\,\psi(\pi,I)(dx)$ of (3.2),
--   2. the predictive law $P^{\pi}(Y_{t+1}\in\cdot\mid I,u)$ and its point masses $P^{\pi}(y\mid I,u)$,
--   3. the shifted window $\mathrm{shift}(I,u,y)$ that drops the oldest entries and appends $u$ and $y$,
--   4. the predictor update $G(\pi,I,u)$ of p. 9, which corrects $\pi$ by the oldest observation and predicts through the oldest action,
--   5. $J^*_\beta(\pi,I)=J^*_\beta(\psi(\pi,I))$, the belief-MDP value read through $\psi$,
--   6. the value $J_\beta(\hat z,\phi)$ of a window policy $\phi$, the fixed point of
--   $$
--   J_\beta(\hat z,\phi)=\hat c(\pi,I,\phi(I))+\beta\sum_{y}P^{\pi}(y\mid I,\phi(I))\,J_\beta\bigl((G(\pi,I,\phi(I)),\mathrm{shift}(I,\phi(I),y)),\phi\bigr).
--   $$
--
--   **Approximate model (3.4)–(3.8), (4.2)–(4.5).** Freezing the predictor at a fixed $\pi^*$ gives $C^*(I,u)=\hat c(\pi^*,I,u)$, the transition weights $P^*(\mathrm{shift}(I,u,y)\mid I,u)=P^{\pi^*}(y\mid I,u)$, the optimal value $J^N_\beta(\pi^*,\cdot)$ of (3.7) and the Q-function $Q^*$ of (4.5), both as value-iteration limits.
--
--   **Filter stability (3.9).** With $\pi^-_t=P(X_t\in\cdot\mid y_{[0,t-1]},u_{[0,t-1]})$ the predictor at time $t$ under the prior $\pi_0^-$ of $X_0$,
--   $$
--   L_t=\sup_{\hat\gamma}E^{\hat\gamma}_{\pi_0^-}\Bigl[\bigl\|P^{\pi^-_t}(X_{t+N}\in\cdot\mid Y_{[t,t+N]},U_{[t,t+N-1]})-P^{\pi^*}(X_{t+N}\in\cdot\mid Y_{[t,t+N]},U_{[t,t+N-1]})\bigr\|_{TV}\Bigr],
--   $$
--   where $\|\mu-\nu\|_{TV}=2\sup_B|\mu(B)-\nu(B)|$ (p. 6).
--
--   **Formalization Note** Windows are stored oldest first. On a window of probability zero the posterior is the zero measure; such windows carry zero weight in every expectation. The supremum in $L_t$ runs over deterministic observation-history policies $u_k=\gamma_k(y_0,\dots,y_k)$, and the expectation is the finite sum over observation histories $y_{[0,t+N]}$ weighted by their probabilities. $\|\cdot\|_{TV}$ is twice the published `MarkovChainCLT.tvDist`. $J^*_\beta$, $J_\beta$, $J^N_\beta$ and $Q^*$ are value-iteration limits.
-- source:
--   Kara, Yüksel, Convergence of finite memory Q learning for POMDPs and near optimality of learned policies under filter stability, arXiv:2103.12158v4, pp. 8–11, 14, §3.1, §3.2, Definition 3.1, (3.1)–(3.9), (4.2)–(4.5)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_FiniteMemQL_Convergence_Model

namespace FiniteMemQL.Convergence

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X Y U : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]

/-- A window of `N + 1` observations and `N` actions, `I = (y_{t−N}, …, y_t; u_{t−N}, …, u_{t−1})`
(§3.1, p. 8, and §4, p. 13), stored **oldest first**: `I.1 j = y_{t−N+j}` for `j ≤ N` and
`I.2 j = u_{t−N+j}` for `j < N`. For `N = 0` the window is the single observation `y_t`. -/
abbrev Window (Y U : Type*) (N : ℕ) := (Fin (N + 1) → Y) × (Fin N → U)

/-- The unnormalised conditional law of the current state given a window, under the prior `π` on
the state at the oldest time of the window: correct by `y_{t−N}`, predict through `u_{t−N}`,
correct by `y_{t−N+1}`, …, correct by `y_t`. Its total mass is `P^π(window observations)` when the
window actions are applied. -/
noncomputable def unnormPost (M : POMDP X Y U) : (N : ℕ) → Measure X → Window Y U N → Measure X
  | 0, π, I => correct M π (I.1 0)
  | N + 1, π, I => unnormPost M N (predict M (correct M π (I.1 0)) (I.2 0)) (Fin.tail I.1, Fin.tail I.2)

/-- The map `ψ(π, I) = P^π(X_t ∈ · | I)` of §3.1, p. 8 (Definition 3.1): the Bayesian update of the
prior `π` on `X_{t−N}` using the window `I`. On a window of probability zero it is the zero
measure. -/
noncomputable def post (M : POMDP X Y U) {N : ℕ} (π : Measure X) (I : Window Y U N) : Measure X :=
  normalize (unnormPost M N π I)

/-- The stage cost `ĉ(π, I, u) = ∫ c(x, u) P^π(dx | I)` of (3.2), p. 8. -/
noncomputable def chat (M : POMDP X Y U) {N : ℕ} (π : Measure X) (I : Window Y U N) (u : U) : ℝ :=
  beliefCost M (post M π I) u

/-- The predictive law `P^π(Y_{t+1} ∈ · | I, u)` of the next observation. -/
noncomputable def predYMeasure (M : POMDP X Y U) {N : ℕ} (π : Measure X) (I : Window Y U N)
    (u : U) : Measure Y :=
  (predict M (post M π I) u).bind M.O

/-- `P^π(y | I, u)`, the probability that the next observation is `y`. -/
noncomputable def predY (M : POMDP X Y U) {N : ℕ} (π : Measure X) (I : Window Y U N) (u : U)
    (y : Y) : ℝ :=
  obsProb M (post M π I) u y

/-- The next window after applying `u` and observing `y`: drop the oldest observation and action,
append `y` and `u`. -/
def shift {N : ℕ} (I : Window Y U N) (u : U) (y : Y) : Window Y U N :=
  (Fin.tail (Fin.snoc (α := fun _ => Y) I.1 y), Fin.tail (Fin.snoc (α := fun _ => U) I.2 u))

/-- The predictor update `G(π, y_{t−N}, u_{t−N})` of p. 9: correct the prior of `X_{t−N}` by the
oldest observation of the window, then predict through the oldest action. For `N = 0` the oldest
action is the current action `u`. -/
noncomputable def nextPrior (M : POMDP X Y U) {N : ℕ} (π : Measure X) (I : Window Y U N) (u : U) :
    Measure X :=
  predict M (normalize (correct M π (I.1 0))) ((Fin.snoc (α := fun _ => U) I.2 u) 0)

/-- `J*_β(ẑ)` for the finite-window state `ẑ = (π, I)`, read through `ψ` as on p. 8:
`J*_β(π, I) = J*_β(ψ(π, I))`. -/
noncomputable def JstarW [Fintype Y] [Fintype U] (M : POMDP X Y U) {N : ℕ} (π : Measure X)
    (I : Window Y U N) : ℝ :=
  Jstar M (post M π I)

/-- Policy evaluation operator of a window policy `φ` on the finite-window belief MDP (last display
of p. 9): `(T_φ W)(π, I) = ĉ(π, I, φ(I)) + β Σ_y P^π(y | I, φ(I)) W(G(π, I, φ(I)), shift(I, φ(I), y))`. -/
noncomputable def polEval [Fintype Y] (M : POMDP X Y U) {N : ℕ} (φ : Window Y U N → U)
    (W : Measure X × Window Y U N → ℝ) (z : Measure X × Window Y U N) : ℝ :=
  chat M z.1 z.2 (φ z.2) + M.β * ∑ y : Y,
    predY M z.1 z.2 (φ z.2) y * W (nextPrior M z.1 z.2 (φ z.2), shift z.2 (φ z.2) y)

/-- `J_β(ẑ, φ)`: the discounted cost of the window policy `φ` from the finite-window state `ẑ`, as
the limit of policy evaluation iterates started from `0`. -/
noncomputable def Jpol [Fintype Y] (M : POMDP X Y U) {N : ℕ} (φ : Window Y U N → U)
    (z : Measure X × Window Y U N) : ℝ :=
  Filter.limUnder Filter.atTop (fun n : ℕ => (polEval M φ)^[n] 0 z)

/-- `C*(I, u) = ĉ(π*, I, u)` ((4.4), p. 14): the approximate model's cost, with predictor `π*`. -/
noncomputable def Cstar (M : POMDP X Y U) {N : ℕ} (πs : Measure X) (I : Window Y U N) (u : U) : ℝ :=
  chat M πs I u

/-- `P*(shift(I, u, y) | I, u) = P^{π*}(y | I, u)` ((3.6), (4.2)–(4.3), p. 14): the approximate
model's transition weight to the next window. -/
noncomputable def Pstar (M : POMDP X Y U) {N : ℕ} (πs : Measure X) (I : Window Y U N) (u : U)
    (y : Y) : ℝ :=
  predY M πs I u y

/-- The optimality operator (3.7) of the approximate finite-window model with predictor fixed to
`π*`. -/
noncomputable def approxBellman [Fintype Y] [Fintype U] (M : POMDP X Y U) {N : ℕ} (πs : Measure X)
    (V : Window Y U N → ℝ) (I : Window Y U N) : ℝ :=
  ⨅ u : U, (Cstar M πs I u + M.β * ∑ y : Y, Pstar M πs I u y * V (shift I u y))

/-- `J^N_β(π*, I)`, the optimal value of the approximate model (3.7), as the value-iteration
limit. -/
noncomputable def JN [Fintype Y] [Fintype U] (M : POMDP X Y U) {N : ℕ} (πs : Measure X)
    (I : Window Y U N) : ℝ :=
  Filter.limUnder Filter.atTop (fun n : ℕ => (approxBellman M πs)^[n] 0 I)

/-- The Q-operator of (4.5): `(T Q)(I, u) = C*(I, u) + β Σ_{I'} P*(I' | I, u) min_v Q(I', v)`. -/
noncomputable def qBellman [Fintype Y] [Fintype U] (M : POMDP X Y U) {N : ℕ} (πs : Measure X)
    (Q : Window Y U N → U → ℝ) (I : Window Y U N) (u : U) : ℝ :=
  Cstar M πs I u + M.β * ∑ y : Y, Pstar M πs I u y * ⨅ v : U, Q (shift I u y) v

/-- `Q*` of (4.5), as the limit of Q-value iteration started from `0`. -/
noncomputable def qStar [Fintype Y] [Fintype U] (M : POMDP X Y U) {N : ℕ} (πs : Measure X)
    (I : Window Y U N) (u : U) : ℝ :=
  Filter.limUnder Filter.atTop (fun n : ℕ => (qBellman M πs)^[n] 0 I u)

/-- A deterministic observation-history policy: the action at time `k` is `γ k (y_0, …, y_k)`. -/
def HistPolicy (Y U : Type*) := (k : ℕ) → (Fin (k + 1) → Y) → U

/-- The actions `u_0, …, u_{n−1}` produced by the history policy `γ` along `y_0, …, y_n`. -/
def histActs (γ : HistPolicy Y U) {n : ℕ} (ys : Fin (n + 1) → Y) : Fin n → U :=
  fun k => γ k (fun j => ys ⟨j, by omega⟩)

/-- `P^γ_{π₀}(Y_0 = y_0, …, Y_n = y_n)`: the probability of the observation history under the prior
`π₀` on `X_0` and the history policy `γ`. -/
noncomputable def histMass (M : POMDP X Y U) (π₀ : Measure X) (γ : HistPolicy Y U) {n : ℕ}
    (ys : Fin (n + 1) → Y) : ℝ :=
  (unnormPost M n π₀ (ys, histActs γ ys) Set.univ).toReal

/-- The filter recursion for the predictor `π⁻_t = P(X_t ∈ · | y_{[0,t−1]}, u_{[0,t−1]})`:
`π⁻_0 = π₀` and `π⁻_{t+1} = predict(normalize(correct(π⁻_t, y_t)), u_t)`. -/
noncomputable def filterPred (M : POMDP X Y U) (π₀ : Measure X) (ys : ℕ → Y) (us : ℕ → U) :
    ℕ → Measure X
  | 0 => π₀
  | t + 1 => predict M (normalize (correct M (filterPred M π₀ ys us t) (ys t))) (us t)

/-- Extension of a finite history `y_0, …, y_n` to a sequence (by repeating `y_n`); only the
entries with index `≤ n` are ever used. -/
def extSeq {n : ℕ} (ys : Fin (n + 1) → Y) : ℕ → Y :=
  fun k => if h : k < n + 1 then ys ⟨k, h⟩ else ys (Fin.last n)

/-- The predictor `π⁻_t` along the history `y_0, …, y_n` (`t ≤ n`) under the prior `π₀` and the
history policy `γ`. -/
noncomputable def predictor (M : POMDP X Y U) (π₀ : Measure X) (γ : HistPolicy Y U) {n : ℕ}
    (t : ℕ) (ys : Fin (n + 1) → Y) : Measure X :=
  filterPred M π₀ (extSeq ys) (fun k => γ k (fun j => extSeq ys j)) t

/-- The window `(Y_{[t,t+N]}, U_{[t,t+N−1]})` inside the history `y_0, …, y_{t+N}`. -/
def windowAt {N : ℕ} (γ : HistPolicy Y U) (t : ℕ) (ys : Fin (t + N + 1) → Y) : Window Y U N :=
  (fun j => ys ⟨t + j, by omega⟩, fun j => histActs γ ys ⟨t + j, by omega⟩)

/-- The filter-stability term `L_t` of (3.9), p. 11:
`L_t = sup_γ E^γ_{π₀}[ ‖P^{π⁻_t}(X_{t+N} ∈ · | Y_{[t,t+N]}, U_{[t,t+N−1]}) − P^{π*}(X_{t+N} ∈ · | Y_{[t,t+N]}, U_{[t,t+N−1]})‖_TV ]`,
the supremum over deterministic observation-history policies, the expectation written as the sum
over the observation histories `y_0, …, y_{t+N}`, and `‖μ − ν‖_TV = 2 sup_B |μ(B) − ν(B)|`
(p. 6), i.e. twice `MarkovChainCLT.tvDist`. -/
noncomputable def Lterm [Fintype Y] [DecidableEq Y] (M : POMDP X Y U) (πs π₀ : Measure X)
    (N t : ℕ) : ℝ :=
  ⨆ γ : HistPolicy Y U, ∑ ys : Fin (t + N + 1) → Y, histMass M π₀ γ ys *
    (2 * MarkovChainCLT.tvDist (post M (predictor M π₀ γ t ys) (windowAt γ t ys))
      (post M πs (windowAt γ t ys)))

end FiniteMemQL.Convergence



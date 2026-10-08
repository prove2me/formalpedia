-- Prove2me | Definitions.Def_ClosedLoopMFG_Converse_Game
-- name    : ClosedLoopMFG_Converse_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T04:28:15.234059+00:00
-- url     : https://prove2.me/theorems/9c356beb-f516-45ac-85da-6368007f70da
-- title:
--   The $n$-player game: Markovian and relaxed Markovian controls, weak solutions, payoffs, Markovian $\epsilon$-Nash equilibria
-- statement:
--   Fix $n\ge1$, a horizon $T>0$, an action set $A$, an initial law $\lambda\in\mathcal P(\mathbb R^d)$ and coefficients $b,f,g$ as in the model.
--
--   1. **Controls.** A *Markovian control* is a Borel map $\tilde\alpha:[0,T]\times(\mathbb R^d)^n\to A$. A *relaxed Markovian control* is a measurable map $\tilde\Lambda:[0,T]\times(\mathbb R^d)^n\to\mathcal P(A)$. Given a single-player feedback $\Lambda^*:[0,T]\times\mathbb R^d\to\mathcal P(A)$, the *symmetric profile* is $\Lambda^{n,i}(t,x)=\Lambda^*(t,x^i)$.
--   2. **State system.** For a profile $\alpha=(\alpha^1,\dots,\alpha^n)$ of Markovian controls, the state processes solve
--   $$dX^i_t=b\big(t,X^i_t,\mu^n_t,\alpha^i(t,X_t)\big)\,dt+dW^i_t,\qquad \mu^n_t=\frac1n\sum_{k=1}^n\delta_{X^k_t},$$
--   where $X_t=(X^1_t,\dots,X^n_t)$. For relaxed profiles, the drift is replaced by $\int_A b(t,X^i_t,\mu^n_t,a)\,\Lambda^i(t,X_t)(da)$.
--   3. **Weak solution.** A weak solution of such a system is a filtered probability space carrying the following:
--      - independent $\mathbb F$-Brownian motions $W^1,\dots,W^n$;
--      - continuous $\mathbb F$-adapted states $X^1,\dots,X^n$ whose initial values are i.i.d. with law $\lambda$ and independent of $(W^1,\dots,W^n)$;
--      - the empirical flow $\mu^n$.
--
--      Almost surely, $X^i_t=X^i_0+\int_0^t(\text{drift})_s\,ds+W^i_t$ for all $i$ and all $t\in[0,T]$.
--   4. **Payoff.** Player $i$'s payoff is
--   $$J^n_i(\alpha)=\mathbb E\Big[\int_0^T f\big(t,X^i_t,\mu^n_t,\alpha^i(t,X_t)\big)\,dt+g(X^i_T,\mu^n_T)\Big]$$
--   (with $\int_A f(\cdot,a)\,\Lambda^i(t,X_t)(da)$ for relaxed controls).
--   5. **Equilibria.** A profile $\alpha$ of Markovian controls is a *Markovian $\epsilon$-Nash equilibrium* when, for every player $i$ and every Markovian control $\beta$,
--   $$J^n_i(\alpha^1,\dots,\alpha^n)\ \ge\ J^n_i(\alpha^1,\dots,\alpha^{i-1},\beta,\alpha^{i+1},\dots,\alpha^n)-\epsilon .$$
--   A *relaxed Markovian $\epsilon$-Nash equilibrium* is the same notion with relaxed Markovian controls and relaxed Markovian deviations.
--
--   Also defined: the law of $\mu^n=\mu^n[\alpha]$ on $C([0,T];\mathcal P(\mathbb R^d))$, and the law of $X=X[\alpha]$ on $(\mathcal C^d)^n$.
--
--   These are the objects that Theorems 2.11 and 3.10 produce in the limit $n\to\infty$.
--
--   **Formalization Note** The paper's SDEs have unit volatility (footnote 4), so each state equation is stated pathwise as an integral equation plus $W^i$; no stochastic integral is involved. The paper defines $J^n_i$ on "the unique in law solution" (p. 6). Here payoffs are functions of a solution, and the Nash inequality is required for every solution of the equilibrium system and every solution of the deviated system. This coincides with the paper's definition because these solutions exist and are unique in law (Girsanov; strong existence for Markovian controls by Veretennikov, as the paper recalls on p. 6). Theorems that assert the existence of an equilibrium therefore also assert that its state system has a solution. Controls are defined at all real times; only $[0,T]$ matters. The empirical flow is carried as a field together with the identity $\mu^n_t=\frac1n\sum_k\delta_{X^k_t}$, which determines it.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 6 (Section 2.1, Definition 2.1), p. 15 (Section 3.1, Definition 3.1), p. 43 (Section 7.1, Λ^{n,i})

import Mathlib
import Definitions.Def_ClosedLoopMFG_Converse_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.Converse

/-- The vector of the `n` states at real time `t`. -/
noncomputable def stateAt {n d : ℕ} {T : ℝ≥0} (x : Fin n → ClosedLoopMFG.Limit.Path d T) (t : ℝ) : Fin n → ClosedLoopMFG.Limit.E d :=
  fun k => ev (x k) t

/-- A Markovian control of the `n`-player game (§2.1, p. 6): a Borel map
`α̃ : [0, T] × (ℝ^d)^n → A`, extended to all real times (only `[0, T]` matters). -/
def IsMarkovControl {n d : ℕ} (T : ℝ≥0) {EA : Type} [MeasurableSpace EA] (A : Set EA)
    (α : ℝ → (Fin n → ClosedLoopMFG.Limit.E d) → EA) : Prop :=
  Measurable (Function.uncurry α) ∧ ∀ t ∈ Set.Icc 0 (T : ℝ), ∀ x, α t x ∈ A

/-- A relaxed Markovian control (§3.1, p. 15): a measurable map
`Λ̃ : [0, T] × (ℝ^d)^n → P(A)`. -/
def IsRelaxedMarkovControl {n d : ℕ} {EA : Type} [TopologicalSpace EA] [MeasurableSpace EA]
    [BorelSpace EA] {A : Set EA} (Λ : ℝ → (Fin n → ClosedLoopMFG.Limit.E d) → PA A) : Prop :=
  Measurable (Function.uncurry Λ)

/-- The symmetric relaxed Markovian profile `Λ^{n,i}(t, x) = Λ*(t, x^i)` built from a
single-player feedback `Λ*` (§7.1, p. 43). -/
def symProfile {n d : ℕ} {EA : Type} [TopologicalSpace EA] [MeasurableSpace EA] {A : Set EA}
    (Λs : ℝ → ClosedLoopMFG.Limit.E d → PA A) : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.E d) → PA A :=
  fun i t x => Λs t (x i)

/-- Drift functionals of the `n`-player system under a Markovian profile `α`:
player `i` has drift `b(t, X^i_t, μ^n_t, α^i(t, X_t))`. -/
noncomputable def driftM {n d : ℕ} [NeZero n] (T : ℝ≥0) {EA : Type}
    (b : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ClosedLoopMFG.Limit.E d) (α : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.E d) → EA) :
    Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → ClosedLoopMFG.Limit.E d :=
  fun i t x => b t (stateAt x t i) (empirical (stateAt x t)) (α i t (stateAt x t))

/-- Running reward functionals under a Markovian profile: `f(t, X^i_t, μ^n_t, α^i(t, X_t))`. -/
noncomputable def runM {n d : ℕ} [NeZero n] (T : ℝ≥0) {EA : Type}
    (f : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ℝ) (α : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.E d) → EA) :
    Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → ℝ :=
  fun i t x => f t (stateAt x t i) (empirical (stateAt x t)) (α i t (stateAt x t))

/-- Drift functionals under a relaxed Markovian profile `Λ`:
`∫_A b(t, X^i_t, μ^n_t, a) Λ^i(t, X_t)(da)`. -/
noncomputable def driftR {n d : ℕ} [NeZero n] (T : ℝ≥0) {EA : Type} [TopologicalSpace EA]
    [MeasurableSpace EA] {A : Set EA} (b : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ClosedLoopMFG.Limit.E d)
    (Λ : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.E d) → PA A) : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → ClosedLoopMFG.Limit.E d :=
  fun i t x => ∫ a, b t (stateAt x t i) (empirical (stateAt x t)) (a : EA)
    ∂(Λ i t (stateAt x t)).meas

/-- Running reward functionals under a relaxed Markovian profile:
`∫_A f(t, X^i_t, μ^n_t, a) Λ^i(t, X_t)(da)`. -/
noncomputable def runR {n d : ℕ} [NeZero n] (T : ℝ≥0) {EA : Type} [TopologicalSpace EA]
    [MeasurableSpace EA] {A : Set EA} (f : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ℝ)
    (Λ : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.E d) → PA A) : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → ℝ :=
  fun i t x => ∫ a, f t (stateAt x t i) (empirical (stateAt x t)) (a : EA)
    ∂(Λ i t (stateAt x t)).meas

/-- Terminal reward functionals: `g(X^i_T, μ^n_T)`. -/
noncomputable def termR {n d : ℕ} [NeZero n] (T : ℝ≥0) (g : ClosedLoopMFG.Limit.E d → PR d → ℝ) :
    Fin n → (Fin n → ClosedLoopMFG.Limit.Path d T) → ℝ :=
  fun i x => g (ev (x i) T) (empirical (stateAt x T))

/-- A weak solution of the `n`-player state system with drift functionals `B` (§2.1, p. 6;
unit volatility, footnote 4): a filtered probability space carrying independent
`𝔽`-Brownian motions `W^1, …, W^n` and continuous `𝔽`-adapted states `X^1, …, X^n` with
i.i.d. initial states of law `λ`, independent of `(W^1, …, W^n)`, such that almost surely
`X^i_t = X^i_0 + ∫_0^t B^i(s, X) ds + W^i_t` for all `i` and `t ∈ [0, T]`. The empirical
measure flow `μ^n_t = (1/n) ∑_k δ_{X^k_t}` is carried as the field `μ`. -/
structure NSol (n d : ℕ) [NeZero n] (T : ℝ≥0) (lam : PR d)
    (B : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → ClosedLoopMFG.Limit.E d) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  [isProb : IsProbabilityMeasure P]
  𝓕 : Filtration ℝ≥0 mΩ
  W : Fin n → ℝ≥0 → Ω → ClosedLoopMFG.Limit.E d
  hW : ∀ i, IsFBrownian 𝓕 P (W i)
  indepW : iIndepFun (fun i ω t => W i t ω) P
  X : Ω → Fin n → ClosedLoopMFG.Limit.Path d T
  measX : Measurable X
  adaptedX : ∀ i (s : Set.Icc (0 : ℝ) T), Measurable[𝓕 (s : ℝ).toNNReal] (fun ω => X ω i s)
  law0 : ∀ i, P.map (fun ω => ev (X ω i) 0) = lam.meas
  iid0 : iIndepFun (fun i ω => ev (X ω i) 0) P
  indep0W : IndepFun (fun ω i => ev (X ω i) 0) (fun ω i t => W i t ω) P
  μ : Ω → Flow d T
  measμ : Measurable μ
  hμ : ∀ ω (s : Set.Icc (0 : ℝ) T), μ ω s = empirical (fun k => X ω k s)
  eqn : ∀ᵐ ω ∂P, ∀ i, ∀ t : Set.Icc (0 : ℝ) T,
    X ω i t = ev (X ω i) 0 + (∫ s in (0 : ℝ)..t, B i s (X ω)) + W i (t : ℝ).toNNReal ω

attribute [instance] NSol.mΩ NSol.isProb

/-- The expected reward of player `i` on a solution `S`:
`E[∫_0^T F^i(t, X) dt + G^i(X)]`. -/
noncomputable def NSol.payoff {n d : ℕ} [NeZero n] {T : ℝ≥0} {lam : PR d}
    {B : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → ClosedLoopMFG.Limit.E d} (S : NSol n d T lam B) (i : Fin n)
    (F : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → ℝ) (G : Fin n → (Fin n → ClosedLoopMFG.Limit.Path d T) → ℝ) : ℝ :=
  ∫ ω, ((∫ t in (0 : ℝ)..T, F i t (S.X ω)) + G i (S.X ω)) ∂S.P

/-- The law of the empirical measure flow `μ^n` of a solution, on `C([0, T]; P(ℝ^d))`. -/
noncomputable def NSol.law {n d : ℕ} [NeZero n] {T : ℝ≥0} {lam : PR d}
    {B : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → ClosedLoopMFG.Limit.E d} (S : NSol n d T lam B) :
    ProbabilityMeasure (Flow d T) :=
  ⟨S.P.map S.μ, Measure.isProbabilityMeasure_map S.measμ.aemeasurable⟩

/-- The law of the state vector `X = (X^1, …, X^n)` of a solution, on `(C^d)^n`. -/
noncomputable def NSol.lawX {n d : ℕ} [NeZero n] {T : ℝ≥0} {lam : PR d}
    {B : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → ClosedLoopMFG.Limit.E d} (S : NSol n d T lam B) :
    Measure (Fin n → ClosedLoopMFG.Limit.Path d T) :=
  S.P.map S.X

/-- A Markovian `ε`-Nash equilibrium (Definition 2.1, p. 6): every `α^i` is Markovian, and for
every player `i` and every Markovian `β`, `J^n_i(α) ≥ J^n_i(α^{-i}, β) − ε`, the payoffs being
computed on any solutions of the two state systems. -/
def IsMarkovNash {n d : ℕ} [NeZero n] (T : ℝ≥0) {EA : Type} [MeasurableSpace EA]
    (A : Set EA) (lam : PR d) (b : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ClosedLoopMFG.Limit.E d) (f : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ℝ)
    (g : ClosedLoopMFG.Limit.E d → PR d → ℝ) (ε : ℝ) (α : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.E d) → EA) : Prop :=
  (∀ i, IsMarkovControl T A (α i)) ∧
  ∀ (i : Fin n) (β : ℝ → (Fin n → ClosedLoopMFG.Limit.E d) → EA), IsMarkovControl T A β →
    ∀ (S : NSol n d T lam (driftM T b α))
      (S' : NSol n d T lam (driftM T b (Function.update α i β))),
      S'.payoff i (runM T f (Function.update α i β)) (termR T g) - ε ≤
        S.payoff i (runM T f α) (termR T g)

/-- A relaxed Markovian `ε`-Nash equilibrium (Definition 3.1, p. 15): the same with relaxed
Markovian controls and relaxed Markovian deviations. -/
def IsRelaxedMarkovNash {n d : ℕ} [NeZero n] (T : ℝ≥0) {EA : Type} [TopologicalSpace EA]
    [MeasurableSpace EA] [BorelSpace EA] (A : Set EA) (lam : PR d)
    (b : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ClosedLoopMFG.Limit.E d) (f : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ℝ)
    (g : ClosedLoopMFG.Limit.E d → PR d → ℝ) (ε : ℝ) (Λ : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.E d) → PA A) : Prop :=
  (∀ i, IsRelaxedMarkovControl (Λ i)) ∧
  ∀ (i : Fin n) (β : ℝ → (Fin n → ClosedLoopMFG.Limit.E d) → PA A), IsRelaxedMarkovControl β →
    ∀ (S : NSol n d T lam (driftR T b Λ))
      (S' : NSol n d T lam (driftR T b (Function.update Λ i β))),
      S'.payoff i (runR T f (Function.update Λ i β)) (termR T g) - ε ≤
        S.payoff i (runR T f Λ) (termR T g)

end ClosedLoopMFG.Converse



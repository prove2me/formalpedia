-- Prove2me | Definitions.Def_ClosedLoopMFG_SignGame_Game
-- name    : ClosedLoopMFG_SignGame_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T05:22:30.130991+00:00
-- url     : https://prove2.me/theorems/ac9445d9-2f57-4ee2-b68e-c3cebad429c8
-- title:
--   The n-player game: controls, weak solutions, payoffs and Markovian ε-Nash equilibria (Section 2.1, Definition 2.1)
-- statement:
--   Fix $n\ge1$, $d\ge0$, $T>0$, a control set $A$ in a real normed space, an initial law $\lambda\in\mathcal P(\mathbb R^d)$, and coefficients
--
--   $$
--   b:[0,T]\times\mathbb R^d\times\mathcal P(\mathbb R^d)\times A\to\mathbb R^d,\quad f:[0,T]\times\mathbb R^d\times\mathcal P(\mathbb R^d)\times A\to\mathbb R,\quad g:\mathbb R^d\times\mathcal P(\mathbb R^d)\to\mathbb R.
--   $$
--
--   **Controls.** An admissible control is a Borel map $\alpha:[0,T]\times(\mathcal C^d)^n\to A$ that is non-anticipative: $\alpha(t,x)=\alpha(t,x')$ whenever $x_s=x'_s$ for all $s\le t$. A Markovian control is a Borel map $\tilde\alpha:[0,T]\times(\mathbb R^d)^n\to A$, acting on paths through $\alpha(t,x)=\tilde\alpha(t,x_t)$. Assumption A ($A$ compact convex; $b,f,g$ bounded and jointly continuous) is recorded as a separate predicate and is **not** built into anything below.
--
--   **States.** For a profile $\alpha=(\alpha_1,\dots,\alpha_n)$, a weak solution of the $n$-player system consists of a filtered probability space carrying independent $\mathbb F$-Brownian motions $W^1,\dots,W^n$ and adapted continuous processes $X^1,\dots,X^n$ such that $X^1_0,\dots,X^n_0$ are i.i.d. with law $\lambda$, independent of $(W^1,\dots,W^n)$, and almost surely, for all $i$ and $t\in[0,T]$,
--
--   $$
--   X^i_t=X^i_0+\int_0^t b\big(s,X^i_s,\mu^n_s,\alpha_i(s,X)\big)\,ds+W^i_t,\qquad \mu^n_s=\frac1n\sum_{k=1}^n\delta_{X^k_s}.
--   $$
--
--   **Payoffs.** Player $i$'s payoff on such a solution is
--
--   $$
--   J^n_i=\mathbb E\Big[\int_0^T f\big(t,X^i_t,\mu^n_t,\alpha_i(t,X)\big)\,dt+g\big(X^i_T,\mu^n_T\big)\Big].
--   $$
--
--   **Equilibria.** For $\varepsilon\ge0$, a profile of Markovian controls is a **Markovian $\varepsilon$-Nash equilibrium** if for every player $i$ and every Markovian control $\beta$,
--
--   $$
--   J^n_i(\alpha_1,\dots,\alpha_n)\ \ge\ J^n_i(\alpha_1,\dots,\alpha_{i-1},\beta,\alpha_{i+1},\dots,\alpha_n)-\varepsilon .
--   $$
--
--   This is the game whose approximate equilibria the paper studies; the sign game of Section 7.3 is one instance of it.
--
--   **Formalization Note** The paper's SDE $dX^i_t=b(\dots)dt+dW^i_t$ has unit volatility (footnote 4, p. 6), so it is written pathwise as the integral equation above, with a Lebesgue integral. The paper speaks of *the* unique-in-law solution; here a solution is an explicit structure, and the Nash inequality is required for **every** solution under $\alpha$ and **every** solution under the deviation. Since solutions exist and are unique in law (Section 2.1, p. 6), this is the paper's definition. Players are indexed by `Fin n` with $n\ne0$. Controls and coefficients take real times; $A$-valuedness is required for $t\in[0,T]$. The payoff is a Bochner integral, which is $0$ for a non-integrable integrand; for bounded $g$ (Assumption A) it is always integrable, and for the sign game of this mission integrability is a fact to be proved, see the mission description.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, pp. 6–7, Section 2.1, Assumption A, footnotes 3–4, Definition 2.1

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_ClosedLoopMFG_SignGame_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.SignGame

variable {EA : Type} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA]
  [BorelSpace EA]

/-- Assumption A (p. 6): `A` is a compact convex subset of a normed space, and `b`, `f`, `g` are
bounded and jointly continuous on `[0, T] × ℝ^d × P(ℝ^d) × A`. Stated separately: nothing in the
n-player game below assumes it. -/
def AssumptionA (T : ℝ≥0) {d : ℕ} (A : Set EA)
    (b : ℝ → EthierKurtz.SDEState d → PR d → EA → EthierKurtz.SDEState d)
    (f : ℝ → EthierKurtz.SDEState d → PR d → EA → ℝ)
    (g : EthierKurtz.SDEState d → PR d → ℝ) : Prop :=
  IsCompact A ∧ Convex ℝ A ∧
  (∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x m, ∀ a ∈ A, ‖b t x m a‖ ≤ C ∧ |f t x m a| ≤ C) ∧
  (∃ C : ℝ, ∀ x m, |g x m| ≤ C) ∧
  ContinuousOn (fun p : ℝ × EthierKurtz.SDEState d × PR d × EA => b p.1 p.2.1 p.2.2.1 p.2.2.2)
    (Set.Icc (0 : ℝ) T ×ˢ Set.univ ×ˢ Set.univ ×ˢ A) ∧
  ContinuousOn (fun p : ℝ × EthierKurtz.SDEState d × PR d × EA => f p.1 p.2.1 p.2.2.1 p.2.2.2)
    (Set.Icc (0 : ℝ) T ×ˢ Set.univ ×ˢ Set.univ ×ˢ A) ∧
  Continuous (fun p : EthierKurtz.SDEState d × PR d => g p.1 p.2)

/-- An admissible (closed-loop, path-dependent) control `α : [0, T] × (𝒞^d)^n → A`
(Section 2.1 and footnote 3, p. 6): Borel, `A`-valued on `[0, T]`, and non-anticipative. -/
def IsAdmissible {n d : ℕ} (T : ℝ≥0) (A : Set EA) (α : ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → EA) : Prop :=
  Measurable (Function.uncurry α) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, α t x ∈ A) ∧
  ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x x' : Fin n → ClosedLoopMFG.Limit.Path d T,
    (∀ k (s : Set.Icc (0 : ℝ) T), (s : ℝ) ≤ t → x k s = x' k s) → α t x = α t x'

/-- A Markovian control (Section 2.1, p. 6): a Borel function `α̃ : [0, T] × (ℝ^d)^n → A`.
Time is real; only `t ∈ [0, T]` is ever used, and `A`-valuedness is asked there. -/
def IsMarkovianControl {n d : ℕ} (T : ℝ≥0) (A : Set EA)
    (α : ℝ → (Fin n → EthierKurtz.SDEState d) → EA) : Prop :=
  Measurable (Function.uncurry α) ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, α t x ∈ A

/-- A Markovian control acting on paths: `α(t, x) = α̃(t, x_t)`. -/
noncomputable def markovAct {n d : ℕ} {T : ℝ≥0}
    (α : ℝ → (Fin n → EthierKurtz.SDEState d) → EA) : ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → EA :=
  fun t x => α t (fun k => ev (x k) t)

/-- A profile of Markovian controls acting on paths. -/
noncomputable def markovProfile {n d : ℕ} {T : ℝ≥0}
    (α : Fin n → ℝ → (Fin n → EthierKurtz.SDEState d) → EA) :
    Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → EA :=
  fun i => markovAct (T := T) (α i)

/-- The drift of player `i` under a strict profile `α`:
`b(t, X^i_t, μ^n_t, α_i(t, X))`. -/
noncomputable def driftOf {n d : ℕ} [NeZero n] {T : ℝ≥0}
    (b : ℝ → EthierKurtz.SDEState d → PR d → EA → EthierKurtz.SDEState d)
    (α : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → EA) :
    Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → EthierKurtz.SDEState d :=
  fun i t x => b t (ev (x i) t) (empirical fun k => ev (x k) t) (α i t x)

/-- The running reward of player `i` under a strict profile `α`:
`f(t, X^i_t, μ^n_t, α_i(t, X))`. -/
noncomputable def runOf {n d : ℕ} [NeZero n] {T : ℝ≥0}
    (f : ℝ → EthierKurtz.SDEState d → PR d → EA → ℝ)
    (α : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → EA) : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → ℝ :=
  fun i t x => f t (ev (x i) t) (empirical fun k => ev (x k) t) (α i t x)

/-- The terminal reward of player `i`: `g(X^i_T, μ^n_T)`. -/
noncomputable def termOf {n d : ℕ} [NeZero n] {T : ℝ≥0}
    (g : EthierKurtz.SDEState d → PR d → ℝ) : Fin n → (Fin n → ClosedLoopMFG.Limit.Path d T) → ℝ :=
  fun i x => g (x i (tend T)) (empirical fun k => x k (tend T))

/-- A weak solution of the n-player state system (Section 2.1, p. 6) with drift functionals
`B i : [0, T] × (𝒞^d)^n → ℝ^d` and unit volatility, written pathwise:
`X^i_t = X^i_0 + ∫_0^t B_i(s, X) ds + W^i_t`. The `W^i` are independent `𝔽`-Brownian motions,
the `X^i_0` are i.i.d. with law `lam` and independent of `(W^1, …, W^n)`, and `μ` is the
empirical measure flow `μ_t = (1/n) Σ_k δ_{X^k_t}`. -/
structure NSol (n d : ℕ) [NeZero n] (T : ℝ≥0) (lam : PR d)
    (B : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → EthierKurtz.SDEState d) where
  /-- the probability space -/
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  /-- the probability measure -/
  P : Measure Ω
  [hP : IsProbabilityMeasure P]
  /-- the filtration -/
  𝓕 : Filtration ℝ≥0 mΩ
  /-- the Brownian motions -/
  W : Fin n → ℝ≥0 → Ω → EthierKurtz.SDEState d
  hW : ∀ i, IsFBrownian 𝓕 P (W i)
  hW_indep : iIndepFun (fun i ω => fun t : ℝ≥0 => W i t ω) P
  /-- the state processes, as a random vector of paths -/
  X : Ω → Fin n → ClosedLoopMFG.Limit.Path d T
  hX_meas : Measurable X
  hX_adapted : ∀ i, ∀ s : Set.Icc (0 : ℝ) T,
    Measurable[𝓕 (s : ℝ).toNNReal] (fun ω => X ω i s)
  hX0_law : ∀ i, P.map (fun ω => X ω i (tzero T)) = lam.meas
  hX0_iid : iIndepFun (fun i ω => X ω i (tzero T)) P
  hX0_W : IndepFun (fun ω i => X ω i (tzero T)) (fun ω i (t : ℝ≥0) => W i t ω) P
  /-- the empirical measure flow -/
  μ : Ω → ClosedLoopMFG.Converse.Flow d T
  hμ_meas : Measurable μ
  hμ : ∀ ω s, μ ω s = empirical (fun k => X ω k s)
  hstate : ∀ᵐ ω ∂P, ∀ i, ∀ t : Set.Icc (0 : ℝ) T,
    X ω i t = X ω i (tzero T) + (∫ s in (0 : ℝ)..(t : ℝ), B i s (X ω)) + W i (t : ℝ).toNNReal ω

attribute [instance] NSol.mΩ NSol.hP

/-- The payoff `J^n_i = E[∫_0^T F_i(t, X) dt + G_i(X)]` of player `i` on a solution `S`. -/
noncomputable def payoff {n d : ℕ} [NeZero n] {T : ℝ≥0} {lam : PR d}
    {B : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → EthierKurtz.SDEState d} (S : NSol n d T lam B)
    (i : Fin n) (F : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path d T) → ℝ) (G : Fin n → (Fin n → ClosedLoopMFG.Limit.Path d T) → ℝ) :
    ℝ :=
  ∫ ω, ((∫ t in (0 : ℝ)..(T : ℝ), F i t (S.X ω)) + G i (S.X ω)) ∂S.P

/-- A Markovian `ε`-Nash equilibrium (Definition 2.1, p. 6): every `α i` is a Markovian control,
and for every player `i`, every Markovian deviation `β`, every solution `S` under `α` and every
solution `S'` under `(α_{-i}, β)`, `J_i(S) ≥ J_i(S') − ε`. -/
def IsMarkovianNash {n d : ℕ} [NeZero n] (T : ℝ≥0) (lam : PR d) (A : Set EA)
    (b : ℝ → EthierKurtz.SDEState d → PR d → EA → EthierKurtz.SDEState d)
    (f : ℝ → EthierKurtz.SDEState d → PR d → EA → ℝ)
    (g : EthierKurtz.SDEState d → PR d → ℝ) (ε : ℝ)
    (α : Fin n → ℝ → (Fin n → EthierKurtz.SDEState d) → EA) : Prop :=
  (∀ i, IsMarkovianControl T A (α i)) ∧
  ∀ i (β : ℝ → (Fin n → EthierKurtz.SDEState d) → EA), IsMarkovianControl T A β →
    ∀ (S : NSol n d T lam (driftOf b (markovProfile (T := T) α)))
      (S' : NSol n d T lam (driftOf b (markovProfile (T := T) (Function.update α i β)))),
      payoff S' i (runOf f (markovProfile (T := T) (Function.update α i β))) (termOf g) - ε ≤
        payoff S i (runOf f (markovProfile (T := T) α)) (termOf g)

end ClosedLoopMFG.SignGame



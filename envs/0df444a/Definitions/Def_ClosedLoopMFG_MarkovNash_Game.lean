-- Prove2me | Definitions.Def_ClosedLoopMFG_MarkovNash_Game
-- name    : ClosedLoopMFG_MarkovNash_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:30:50.604916+00:00
-- url     : https://prove2.me/theorems/2ed8c925-1382-4693-8a9a-a4b37470e037
-- title:
--   The $n$-player game: admissible and Markovian controls, weak solutions, payoffs $J^n_i$, closed-loop and Markovian $\epsilon$-Nash equilibria (Section 2.1, Definition 2.1)
-- statement:
--   Fix $n\ge1$, $d$, $T>0$, the data $(A,b,f,g)$ and an initial law $\lambda\in\mathcal P(\mathbb R^d)$.
--
--   1. An **admissible (closed-loop, path-dependent) control** is a Borel map $\alpha:[0,T]\times(\mathcal C^d)^n\to A$ that is non-anticipative: $\alpha(t,\boldsymbol x)=\alpha(t,\boldsymbol x')$ whenever $\boldsymbol x_s=\boldsymbol x'_s$ for all $s\le t$. $\mathcal A_n$ is the set of admissible controls.
--   2. A **Markovian control** is a Borel map $\tilde\alpha:[0,T]\times(\mathbb R^d)^n\to A$; it acts as the admissible control $\alpha(t,\boldsymbol x)=\tilde\alpha(t,\boldsymbol x_t)$. $\mathcal{AM}_n$ is the set of Markovian controls.
--   3. For a profile $\boldsymbol\alpha=(\alpha^1,\dots,\alpha^n)$ the state processes solve
--   $$dX^i_t=b(t,X^i_t,\mu^n_t,\alpha^i(t,\boldsymbol X))\,dt+dW^i_t,\qquad \mu^n_t=\frac1n\sum_{k=1}^n\delta_{X^k_t},$$
--   where $W^1,\dots,W^n$ are independent $d$-dimensional Brownian motions and $X^1_0,\dots,X^n_0$ are i.i.d. with law $\lambda$, independent of $(W^1,\dots,W^n)$.
--   4. Player $i$'s payoff is
--   $$J^n_i(\alpha^1,\dots,\alpha^n)=\mathbb E\Big[\int_0^T f(t,X^i_t,\mu^n_t,\alpha^i(t,\boldsymbol X))\,dt+g(X^i_T,\mu^n_T)\Big].$$
--   5. (Definition 2.1) Let $\epsilon\ge0$. $(\alpha^1,\dots,\alpha^n)\in\mathcal A_n^n$ is a **closed-loop $\epsilon$-Nash equilibrium** if for $i=1,\dots,n$
--   $$J^n_i(\alpha^1,\dots,\alpha^n)\ge\sup_{\beta\in\mathcal A_n}J^n_i(\alpha^1,\dots,\alpha^{i-1},\beta,\alpha^{i+1},\dots,\alpha^n)-\epsilon.$$
--   $(\alpha^1,\dots,\alpha^n)\in\mathcal{AM}_n^n$ is a **Markovian $\epsilon$-Nash equilibrium** if the same holds with the supremum over $\beta\in\mathcal{AM}_n$ only.
--
--   These are the two equilibrium notions compared by Proposition 2.2.
--
--   **Formalization Note** The volatility is the identity (footnote 4), so the state equation is stated pathwise: almost surely, for all $t\in[0,T]$, $X^i_t=X^i_0+\int_0^t b(s,X^i_s,\mu^n_s,\alpha^i(s,\boldsymbol X))\,ds+W^i_t$, a Lebesgue integral. A weak solution (structure `NSol`) bundles a probability space $\Omega$ (in `Type`), a filtration $\mathbb F$, Brownian motions $W^i$ that are each $\mathbb F$-Brownian, mutually independent, and jointly have increments independent of $\mathcal F_t$ (so $(W^1,\dots,W^n)$ is an $nd$-dimensional $\mathbb F$-Brownian motion, the standard meaning of "independent Brownian motions" in a weak solution), continuous $\mathbb F$-adapted states $X$, the i.i.d. initial law $\lambda$, independence from the Brownian motions, and the empirical flow $\mu^n$ carried as data with $\mu^n_s=L_n(\boldsymbol X_s)$. The paper defines $J^n_i$ on "the unique in law solution" (Girsanov; p. 6). Here $J^n_i$ is computed on a given solution, and each $\epsilon$-Nash condition is required for every solution of the equilibrium profile and every solution of the deviated profile; this coincides with the paper's definition because solutions exist and are unique in law. Brownian motions are indexed by $t\in[0,\infty)$; a Brownian motion on $[0,T]$ extends, and every statement is about laws. Controls take a real time argument, with values in $A$ and non-anticipation required only for $t\in[0,T]$; Borel measurability is asked jointly on $\mathbb R\times(\mathcal C^d)^n$ (resp. $\mathbb R\times(\mathbb R^d)^n$), which any control on $[0,T]$ satisfies after extension.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 6, Section 2.1 and Definition 2.1 (with footnotes 3–4)

import Mathlib
import Definitions.Def_ClosedLoopMFG_MarkovNash_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ClosedLoopMFG.MarkovNash

variable {n d : ℕ} {T : ℝ≥0} {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA]
  [MeasurableSpace EA]

/-- An **admissible (closed-loop, path-dependent) control** of the `n`-player game (§2.1, p. 6,
footnote 3): a Borel map `α : [0, T] × (𝒞^d)^n → A` with `α(t, x) = α(t, x')` whenever
`x_s = x'_s` for all `s ≤ t`. Time is real; only `t ∈ [0, T]` is constrained. -/
def IsAdmissible (A : Set EA) (α : ℝ → (Fin n → Path d T) → EA) : Prop :=
  Measurable (Function.uncurry α) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, α t x ∈ A) ∧
  ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x x' : Fin n → Path d T,
    (∀ k (s : Set.Icc (0 : ℝ) T), (s : ℝ) ≤ t → x k s = x' k s) → α t x = α t x'

/-- A **Markovian control** (§2.1, p. 6), identified with a Borel map
`α̃ : [0, T] × (ℝ^d)^n → A`. -/
def IsMarkovControl (A : Set EA) (α : ℝ → (Fin n → E d) → EA) : Prop :=
  Measurable (Function.uncurry α) ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, α t x ∈ A

/-- The time-`t` state `x_t = (x^1_t, …, x^n_t) ∈ (ℝ^d)^n` of a path vector `x ∈ (𝒞^d)^n`. -/
noncomputable def snap (x : Fin n → Path d T) (t : ℝ) : Fin n → E d := fun k => ev (x k) t

/-- The closed-loop control `α(t, x) = α̃(t, x_t)` of a Markovian `α̃` (§2.1, p. 6). -/
noncomputable def liftM (α : ℝ → (Fin n → E d) → EA) : ℝ → (Fin n → Path d T) → EA :=
  fun t x => α t (snap x t)

/-- Drift of player `i` under the profile `α`, as a functional of the path vector:
`b(t, x^i_t, μ^n_t, α^i(t, x))` with `μ^n_t = (1/n) ∑_k δ_{x^k_t}` (§2.1, p. 6). -/
noncomputable def drift [NeZero n] (b : ℝ → E d → PR d → EA → E d)
    (α : Fin n → ℝ → (Fin n → Path d T) → EA) : Fin n → ℝ → (Fin n → Path d T) → E d :=
  fun i t x => b t (snap x t i) (empirical (snap x t)) (α i t x)

/-- Running reward of player `i`: `f(t, x^i_t, μ^n_t, α^i(t, x))` (§2.1, p. 6). -/
noncomputable def runR [NeZero n] (f : ℝ → E d → PR d → EA → ℝ)
    (α : Fin n → ℝ → (Fin n → Path d T) → EA) : Fin n → ℝ → (Fin n → Path d T) → ℝ :=
  fun i t x => f t (snap x t i) (empirical (snap x t)) (α i t x)

/-- Terminal reward of player `i`: `g(x^i_T, μ^n_T)` (§2.1, p. 6). -/
noncomputable def termR [NeZero n] (g : E d → PR d → ℝ) : Fin n → (Fin n → Path d T) → ℝ :=
  fun i x => g (x i (tT T)) (empirical fun k => x k (tT T))

/-- A **weak solution of the `n`-player SDE system** (§2.1, p. 6) with drift functionals
`B i : ℝ → (𝒞^d)^n → ℝ^d`, written pathwise (unit volatility, footnote 4):
`X^i_t = X^i_0 + ∫_0^t B^i(s, X) ds + W^i_t` for all `t ∈ [0, T]`, a.s. The data are a filtered
probability space, `n` independent `d`-dimensional `𝔽`-Brownian motions jointly forming an
`nd`-dimensional `𝔽`-Brownian motion, continuous `𝔽`-adapted states with i.i.d. initial
states of law `λ` independent of the Brownian motions, and the empirical flow `μ^n`. -/
structure NSol (n d : ℕ) [NeZero n] (T : ℝ≥0) (lam : PR d)
    (B : Fin n → ℝ → (Fin n → Path d T) → E d) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  [isProb : IsProbabilityMeasure P]
  𝓕 : Filtration ℝ≥0 mΩ
  W : Fin n → ℝ≥0 → Ω → E d
  hW : ∀ i, IsFBrownian 𝓕 P (W i)
  hW_indep : iIndepFun (fun i ω (t : ℝ≥0) => W i t ω) P
  hW_joint : ∀ t, Indep (𝓕 t)
    (MeasurableSpace.comap (fun ω (p : Fin n × Set.Ici t) => W p.1 p.2 ω - W p.1 t ω)
      inferInstance) P
  X : Ω → Fin n → Path d T
  hX_meas : Measurable X
  hX_adapted : ∀ i (s : Set.Icc (0 : ℝ) T), Measurable[𝓕 (s : ℝ).toNNReal] (fun ω => X ω i s)
  hX0_law : ∀ i, P.map (fun ω => X ω i (t0 T)) = (lam.toMeasure)
  hX0_iid : iIndepFun (fun i ω => X ω i (t0 T)) P
  hX0_W : IndepFun (fun ω i => X ω i (t0 T)) (fun ω i (t : ℝ≥0) => W i t ω) P
  μ : Ω → Flow d T
  hμ_meas : Measurable μ
  hμ : ∀ ω s, μ ω s = empirical (fun k => X ω k s)
  hstate : ∀ᵐ ω ∂P, ∀ i (t : Set.Icc (0 : ℝ) T),
    X ω i t = X ω i (t0 T) + (∫ s in (0 : ℝ)..(t : ℝ), B i s (X ω)) + W i (t : ℝ).toNNReal ω

attribute [instance] NSol.mΩ NSol.isProb

/-- Expected reward of player `i` on a solution `S`:
`E[∫_0^T F^i(t, X) dt + G^i(X)]`. -/
noncomputable def payoff [NeZero n] {lam : PR d} {B : Fin n → ℝ → (Fin n → Path d T) → E d}
    (S : NSol n d T lam B) (i : Fin n) (F : Fin n → ℝ → (Fin n → Path d T) → ℝ)
    (G : Fin n → (Fin n → Path d T) → ℝ) : ℝ :=
  ∫ ω, ((∫ t in (0 : ℝ)..(T : ℝ), F i t (S.X ω)) + G i (S.X ω)) ∂S.P

/-- `J^n_i(α)` computed on a solution `S` of the state system of the profile `α` (§2.1, p. 6):
`E[∫_0^T f(t, X^i_t, μ^n_t, α^i(t, X)) dt + g(X^i_T, μ^n_T)]`. -/
noncomputable def Jn [NeZero n] {lam : PR d} (b : ℝ → E d → PR d → EA → E d)
    (f : ℝ → E d → PR d → EA → ℝ) (g : E d → PR d → ℝ)
    (α : Fin n → ℝ → (Fin n → Path d T) → EA) (S : NSol n d T lam (drift b α)) (i : Fin n) : ℝ :=
  payoff S i (runR f α) (termR g)

/-- **Closed-loop `ε`-Nash equilibrium** (Definition 2.1, p. 6): every `α^i` is admissible, and for
every player `i` and every admissible `β`, `J^n_i(α) ≥ J^n_i(α^{-i}, β) − ε`, where both payoffs
are evaluated on any solutions of the respective state systems. -/
def IsClosedLoopNash [NeZero n] (A : Set EA) (lam : PR d) (b : ℝ → E d → PR d → EA → E d)
    (f : ℝ → E d → PR d → EA → ℝ) (g : E d → PR d → ℝ) (ε : ℝ)
    (α : Fin n → ℝ → (Fin n → Path d T) → EA) : Prop :=
  (∀ i, IsAdmissible A (α i)) ∧
  ∀ (i : Fin n) (β : ℝ → (Fin n → Path d T) → EA), IsAdmissible A β →
    ∀ (S : NSol n d T lam (drift b α))
      (S' : NSol n d T lam (drift b (Function.update α i β))),
      Jn b f g α S i ≥ Jn b f g (Function.update α i β) S' i - ε

/-- **Markovian `ε`-Nash equilibrium** (Definition 2.1, p. 6): every `α̃^i` is a Markovian control,
and for every player `i` and every Markovian `β̃`, `J^n_i(α̃) ≥ J^n_i(α̃^{-i}, β̃) − ε`, both
payoffs evaluated on any solutions of the respective state systems. -/
def IsMarkovianNash [NeZero n] (T : ℝ≥0) (A : Set EA) (lam : PR d)
    (b : ℝ → E d → PR d → EA → E d) (f : ℝ → E d → PR d → EA → ℝ) (g : E d → PR d → ℝ) (ε : ℝ)
    (α : Fin n → ℝ → (Fin n → E d) → EA) : Prop :=
  (∀ i, IsMarkovControl (T := T) A (α i)) ∧
  ∀ (i : Fin n) (β : ℝ → (Fin n → E d) → EA), IsMarkovControl (T := T) A β →
    ∀ (S : NSol n d T lam (drift b (fun j => liftM (α j))))
      (S' : NSol n d T lam (drift b (fun j => liftM (Function.update α i β j)))),
      Jn b f g (fun j => liftM (α j)) S i ≥
        Jn b f g (fun j => liftM (Function.update α i β j)) S' i - ε

end ClosedLoopMFG.MarkovNash



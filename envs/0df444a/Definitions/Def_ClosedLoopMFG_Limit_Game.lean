-- Prove2me | Definitions.Def_ClosedLoopMFG_Limit_Game
-- name    : ClosedLoopMFG_Limit_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:30:54.593326+00:00
-- url     : https://prove2.me/theorems/1ca19a15-f48f-4b04-b14f-0bc70cf6ec70
-- title:
--   The $n$-player game: admissible closed-loop controls, weak solutions of the state system, payoffs $J^n_i$, closed-loop $\varepsilon$-Nash equilibria (Section 2.1, Definition 2.1)
-- statement:
--   Let $n\ge1$. An **admissible control** of the $n$-player game is a Borel measurable function $\alpha:[0,T]\times(\mathcal C^d)^n\to A$ which is progressively measurable: $\alpha(t,x)=\alpha(t,x')$ whenever $x_s=x'_s$ for all $s\le t$.
--
--   For a profile $\alpha=(\alpha^1,\dots,\alpha^n)$ of admissible controls, the state processes solve
--   $$dX^i_t=b\big(t,X^i_t,\mu^n_t,\alpha^i(t,X)\big)\,dt+dW^i_t,\qquad \mu^n_t=\frac1n\sum_{k=1}^n\delta_{X^k_t},$$
--   where $W^1,\dots,W^n$ are independent $d$-dimensional Brownian motions and $X^1_0,\dots,X^n_0$ are i.i.d. with law $\lambda$, independent of $(W^1,\dots,W^n)$. A **weak solution** is a filtered probability space carrying these objects: $W=(W^1,\dots,W^n)$ is a Brownian motion for the filtration (its future increments are independent of $\mathcal F_t$), $X$ is continuous and adapted, and the state equation holds. Player $i$'s payoff is
--   $$J^n_i(\alpha)=\mathbb E\Big[\int_0^T f\big(t,X^i_t,\mu^n_t,\alpha^i(t,X)\big)\,dt+g(X^i_T,\mu^n_T)\Big].$$
--   For $\varepsilon\ge0$, a **closed-loop $\varepsilon$-Nash equilibrium** is a profile of admissible controls such that for every player $i$ and every admissible $\beta$,
--   $$J^n_i(\alpha)\ \ge\ J^n_i(\alpha^1,\dots,\alpha^{i-1},\beta,\alpha^{i+1},\dots,\alpha^n)-\varepsilon .$$
--   The law of the empirical measure flow $\mu^n=\mu^n[\alpha]$ on $C([0,T];\mathcal P(\mathbb R^d))$ is the object of the main limit theorem.
--
--   **Formalization Note** The volatility is the identity (footnote 4, p. 6), so the state equation is stated pathwise: almost surely, $X^i_t=X^i_0+\int_0^t b(\dots)\,ds+W^i_t$ for all $t\in[0,T]$; this is a Lebesgue integral of a bounded measurable integrand, and no stochastic integral is involved. The paper defines $J^n_i$ through "the unique in law solution" (by Girsanov's theorem). Here a solution is a structure `NSol` (sample space in `Type`, filtration, Brownian motions, state processes, and the empirical flow carried as a measurable random variable with its defining equation), the payoff is computed on a given solution, and the $\varepsilon$-Nash inequality is required for every solution of the original profile and every solution of the deviated profile; because solutions exist and are unique in law (Section 2.1, p. 6, a milestone of this mission), this is the paper's definition. Players are indexed by `Fin n`; the payoff integral in time is over $[0,T]$, and all conditions on controls are asked for $t\in[0,T]$.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 6, Section 2.1, footnote 3, Definition 2.1

import Mathlib
import Definitions.Def_ClosedLoopMFG_Limit_Model

namespace ClosedLoopMFG.Limit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- An **admissible control** of the `n`-player game (§2.1 and footnote 3, p. 6): a Borel
measurable `α : [0, T] × (𝒞^d)^n → A` that is progressively measurable, i.e. `α(t, x) = α(t, x')`
whenever `x_s = x'_s` for all `s ≤ t`. Time is real; the conditions are asked for `t ∈ [0, T]`. -/
def IsAdmissible {d n : ℕ} {T : ℝ≥0} {EA : Type} [MeasurableSpace EA] (A : Set EA)
    (α : ℝ → (Fin n → Path d T) → EA) : Prop :=
  Measurable (Function.uncurry α) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, α t x ∈ A) ∧
  ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x x' : Fin n → Path d T,
    (∀ k, ∀ s : Set.Icc (0 : ℝ) T, (s : ℝ) ≤ t → x k s = x' k s) → α t x = α t x'

/-- The empirical measure flow `t ↦ (1/n) ∑_k δ_{x^k_t}` of a vector of paths, an element of
`C([0, T]; P(ℝ^d))`. -/
noncomputable def empFlow {d n : ℕ} [NeZero n] {T : ℝ≥0} (x : Fin n → Path d T) : Flow d T :=
  ⟨fun s => empirical (fun k => x k s),
    continuous_empiricalMeasure.comp (continuous_pi fun k => (x k).continuous)⟩

/-- The drift of player `i` under the profile `α`: `b(t, x^i_t, μ^n_t, α^i(t, x))`, with
`μ^n_t = (1/n) ∑_k δ_{x^k_t}` (§2.1, p. 6). -/
noncomputable def drift {d n : ℕ} [NeZero n] {T : ℝ≥0} {EA : Type}
    (b : ℝ → E d → PR d → EA → E d) (α : Fin n → ℝ → (Fin n → Path d T) → EA) :
    Fin n → ℝ → (Fin n → Path d T) → E d :=
  fun i t x => b t (ev (x i) t) (empirical fun k => ev (x k) t) (α i t x)

/-- The running reward of player `i`: `f(t, x^i_t, μ^n_t, α^i(t, x))` (§2.1, p. 6). -/
noncomputable def runRew {d n : ℕ} [NeZero n] {T : ℝ≥0} {EA : Type}
    (f : ℝ → E d → PR d → EA → ℝ) (α : Fin n → ℝ → (Fin n → Path d T) → EA) (i : Fin n) :
    ℝ → (Fin n → Path d T) → ℝ :=
  fun t x => f t (ev (x i) t) (empirical fun k => ev (x k) t) (α i t x)

/-- The terminal reward of player `i`: `g(x^i_T, μ^n_T)` (§2.1, p. 6). -/
noncomputable def termRew {d n : ℕ} [NeZero n] {T : ℝ≥0} (g : E d → PR d → ℝ) (i : Fin n) :
    (Fin n → Path d T) → ℝ :=
  fun x => g (ev (x i) T) (empirical fun k => ev (x k) T)

/-- A **weak solution of the `n`-player state system** (§2.1, p. 6) with drift functionals
`B i : [0, T] × (𝒞^d)^n → ℝ^d` and initial law `λ`: a filtered probability space carrying
independent `𝔽`-Brownian motions `W^1, …, W^n` (jointly: the vector of future increments is
independent of `𝓕_t`), an adapted continuous `(ℝ^d)^n`-valued process `X` whose initial states are
i.i.d. with law `λ` and independent of `(W^1, …, W^n)`, the empirical measure flow `μ^n` of `X`
(carried as a measurable random variable with its defining equation), and the state equation in
pathwise form `X^i_t = X^i_0 + ∫_0^t B^i(s, X) ds + W^i_t` for all `t ∈ [0, T]`, almost surely
(unit volatility, footnote 4). -/
structure NSol (n d : ℕ) [NeZero n] (T : ℝ≥0) (lam : PR d)
    (B : Fin n → ℝ → (Fin n → Path d T) → E d) where
  /-- the sample space -/
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  /-- the probability measure -/
  P : Measure Ω
  [isProb : IsProbabilityMeasure P]
  /-- the filtration -/
  𝓕 : Filtration ℝ≥0 mΩ
  /-- the Brownian motions -/
  W : Fin n → ℝ≥0 → Ω → E d
  hW : ∀ i, EthierKurtz.IsStandardBrownian P (W i)
  adaptW : ∀ i t, Measurable[𝓕 t] (W i t)
  incrW : ∀ t, Indep (𝓕 t)
    (MeasurableSpace.comap (fun ω i (r : Set.Ici t) => W i r ω - W i t ω) inferInstance) P
  indepW : iIndepFun (fun i ω => bmPath (W i) ω) P
  /-- the state processes -/
  X : Ω → Fin n → Path d T
  measX : Measurable X
  adaptX : ∀ s : Set.Icc (0 : ℝ) T, Measurable[𝓕 (s : ℝ).toNNReal] (fun ω k => X ω k s)
  initLaw : ∀ i, P.map (fun ω => ev (X ω i) 0) = lam.meas
  initIndep : iIndepFun (fun i ω => ev (X ω i) 0) P
  initIndepW : IndepFun (fun ω i => ev (X ω i) 0) (fun ω i => bmPath (W i) ω) P
  /-- the empirical measure flow `μ^n` -/
  μ : Ω → Flow d T
  measμ : Measurable μ
  μ_eq : ∀ ω, μ ω = empFlow (X ω)
  state : ∀ᵐ ω ∂P, ∀ i, ∀ t : Set.Icc (0 : ℝ) T,
    X ω i t = ev (X ω i) 0 + (∫ s in (0 : ℝ)..t, B i s (X ω)) + W i (t : ℝ).toNNReal ω

attribute [instance] NSol.mΩ NSol.isProb

/-- The expected reward `E[∫_0^T F(t, X) dt + G(X)]` on a solution. -/
noncomputable def NSol.payoff {n d : ℕ} [NeZero n] {T : ℝ≥0} {lam : PR d}
    {B : Fin n → ℝ → (Fin n → Path d T) → E d} (S : NSol n d T lam B)
    (F : ℝ → (Fin n → Path d T) → ℝ) (G : (Fin n → Path d T) → ℝ) : ℝ :=
  ∫ ω, ((∫ t in (0 : ℝ)..T, F t (S.X ω)) + G (S.X ω)) ∂S.P

/-- The payoff `J^n_i(α) = E[∫_0^T f(t, X^i_t, μ^n_t, α^i(t, X)) dt + g(X^i_T, μ^n_T)]` of player
`i`, computed on the solution `S` of the state system of `α` (§2.1, p. 6). -/
noncomputable def NSol.J {n d : ℕ} [NeZero n] {T : ℝ≥0} {lam : PR d} {EA : Type}
    {B : Fin n → ℝ → (Fin n → Path d T) → E d} (S : NSol n d T lam B)
    (f : ℝ → E d → PR d → EA → ℝ) (g : E d → PR d → ℝ)
    (α : Fin n → ℝ → (Fin n → Path d T) → EA) (i : Fin n) : ℝ :=
  S.payoff (runRew f α i) (termRew g i)

/-- The law of the empirical measure flow `μ^n` of a solution, an element of
`P(C([0, T]; P(ℝ^d)))`. -/
noncomputable def NSol.law {n d : ℕ} [NeZero n] {T : ℝ≥0} {lam : PR d}
    {B : Fin n → ℝ → (Fin n → Path d T) → E d} (S : NSol n d T lam B) :
    ProbabilityMeasure (Flow d T) :=
  ⟨S.P.map S.μ, Measure.isProbabilityMeasure_map S.measμ.aemeasurable⟩

/-- **Closed-loop ε-Nash equilibrium** (Definition 2.1, p. 6): every `α^i` is admissible and, for
every player `i` and every admissible deviation `β`, `J^n_i(α) ≥ J^n_i(α^{-i}, β) − ε`, where each
payoff is computed on any weak solution of the corresponding state system. -/
def IsClosedLoopNash {n d : ℕ} [NeZero n] {T : ℝ≥0} {EA : Type} [MeasurableSpace EA]
    (A : Set EA) (lam : PR d) (b : ℝ → E d → PR d → EA → E d) (f : ℝ → E d → PR d → EA → ℝ)
    (g : E d → PR d → ℝ) (ε : ℝ) (α : Fin n → ℝ → (Fin n → Path d T) → EA) : Prop :=
  (∀ i, IsAdmissible A (α i)) ∧
  ∀ (i : Fin n) (β : ℝ → (Fin n → Path d T) → EA), IsAdmissible A β →
    ∀ (S : NSol n d T lam (drift b α)) (S' : NSol n d T lam (drift b (Function.update α i β))),
      S.J f g α i ≥ S'.J f g (Function.update α i β) i - ε

end ClosedLoopMFG.Limit



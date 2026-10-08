-- Prove2me | Definitions.Def_BertsekasShreve_Generalized_Optimality
-- name    : BertsekasShreve_Generalized_Optimality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:39:20.535794+00:00
-- url     : https://prove2.me/theorems/f3d86948-10eb-47c8-bd37-190db329431e
-- title:
--   Optimal, $N$-stage optimal, uniformly $N$-stage optimal and $\varepsilon$-optimal policies; $\{\varepsilon_n\}$-dominated convergence
-- statement:
--   The terminology of Chapter 2 (p. 29), applied to the generalized model of Chapter 6 with policies in $\tilde\Pi$.
--
--   1. $\pi^*\in\tilde\Pi$ is **$N$-stage optimal** if $J_{N,\pi^*}=J^*_N$; **optimal at $x$** if $J_{\pi^*}(x)=J^*(x)$; **optimal** if $J_{\pi^*}=J^*$.
--   2. $\pi^*=(\mu_0^*,\mu_1^*,\dots)$ is **uniformly $N$-stage optimal** if the tail $(\mu_i^*,\mu_{i+1}^*,\dots)$ is $(N-i)$-stage optimal for every $i=0,1,\dots,N-1$.
--   3. For $\varepsilon>0$, $\pi_\varepsilon$ is **$N$-stage $\varepsilon$-optimal** if
--   $$J_{N,\pi_\varepsilon}(x)\le\begin{cases}J^*_N(x)+\varepsilon&\text{if }J^*_N(x)>-\infty,\\-1/\varepsilon&\text{if }J^*_N(x)=-\infty.\end{cases}$$
--   4. For positive numbers $\varepsilon_n\downarrow0$, a sequence of policies $\{\pi_n\}$ exhibits **$\{\varepsilon_n\}$-dominated convergence to optimality** if $\lim_{n\to\infty}J_{N,\pi_n}=J^*_N$ pointwise and, for $n=2,3,\dots$,
--   $$J_{N,\pi_n}(x)\le\begin{cases}J^*_N(x)+\varepsilon_n&\text{if }J^*_N(x)>-\infty,\\J_{N,\pi_{n-1}}(x)+\varepsilon_n&\text{if }J^*_N(x)=-\infty.\end{cases}$$
--
--   These notions are the targets of the finite-horizon results (Propositions 6.1–6.3) and of the stationary-policy results (Propositions 6.4–6.5).
--
--   **Formalization Note** The book's index $n=1,2,\dots$ of a sequence of policies is Lean's $k=n-1$; "for $n=2,3,\dots$" is the condition on index $k+1$ for every $k$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 29, Section 2.2 (optimal, uniformly N-stage optimal, N-stage ε-optimal, {ε_n}-dominated convergence); p. 93 (terminology carried over to Chapter 6)

import Mathlib
import Definitions.Def_BertsekasShreve_Generalized_Model

namespace BertsekasShreve.Generalized

open Filter Topology

namespace Model

variable {S C : Type*} (P : Model S C)

/-- `π* ∈ Π̃` is `N`-stage optimal if `J_{N,π*} = J*_N` (p. 29). -/
def IsNStageOptimal (N : ℕ) (π : P.Policy) : Prop := P.JN N π = P.JNstar N

/-- `π* = (μ₀*, μ₁*, …)` is uniformly `N`-stage optimal if `(μ_i*, μ_{i+1}*, …)` is
`(N − i)`-stage optimal for all `i = 0, 1, …, N − 1` (p. 29). -/
def IsUniformlyNStageOptimal (N : ℕ) (π : P.Policy) : Prop :=
  ∀ i, i < N → P.IsNStageOptimal (N - i) (P.shift π i)

/-- `π ∈ Π̃` is optimal at `x ∈ S` if `J_π(x) = J*(x)` (p. 29). -/
def IsOptimalAt (π : P.Policy) (x : S) : Prop := P.Jpi π x = P.Jstar x

/-- `π* ∈ Π̃` is optimal if `J_{π*} = J*` (p. 29). -/
def IsOptimal (π : P.Policy) : Prop := P.Jpi π = P.Jstar

/-- Given `ε > 0`, `π_ε ∈ Π̃` is `N`-stage `ε`-optimal (p. 29) if for all `x`,
`J_{N,π_ε}(x) ≤ J*_N(x) + ε` when `J*_N(x) > −∞` and `J_{N,π_ε}(x) ≤ −1/ε` when `J*_N(x) = −∞`. -/
def IsNStageEpsOptimal (N : ℕ) (ε : ℝ) (π : P.Policy) : Prop :=
  ∀ x, (⊥ < P.JNstar N x → P.JN N π x ≤ P.JNstar N x + (ε : EReal)) ∧
    (P.JNstar N x = ⊥ → P.JN N π x ≤ ((-1 / ε : ℝ) : EReal))

/-- `{ε_n}`-dominated convergence to optimality (p. 29). For a sequence of positive numbers
`ε_n ↓ 0`, a sequence of policies `{π_n}` exhibits it if `lim_{n → ∞} J_{N,π_n} = J*_N`
(pointwise in `[−∞, ∞]`) and, for `n = 2, 3, …`,
`J_{N,π_n}(x) ≤ J*_N(x) + ε_n` if `J*_N(x) > −∞` and
`J_{N,π_n}(x) ≤ J_{N,π_{n−1}}(x) + ε_n` if `J*_N(x) = −∞`.
The book's index `n = 1, 2, …` is Lean's `k = n − 1`: `πs k = π_{k+1}`, `ε k = ε_{k+1}`; the
condition "for `n = 2, 3, …`" is the condition on `k + 1` for every `k`. -/
def DominatedConvergence (N : ℕ) (ε : ℕ → ℝ) (πs : ℕ → P.Policy) : Prop :=
  (∀ x, Tendsto (fun k => P.JN N (πs k) x) atTop (𝓝 (P.JNstar N x))) ∧
  ∀ k x,
    (⊥ < P.JNstar N x → P.JN N (πs (k + 1)) x ≤ P.JNstar N x + (ε (k + 1) : EReal)) ∧
    (P.JNstar N x = ⊥ → P.JN N (πs (k + 1)) x ≤ P.JN N (πs k) x + (ε (k + 1) : EReal))

end Model

end BertsekasShreve.Generalized



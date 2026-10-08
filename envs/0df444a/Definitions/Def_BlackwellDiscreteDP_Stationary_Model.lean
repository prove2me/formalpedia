-- Prove2me | Definitions.Def_BlackwellDiscreteDP_Stationary_Model
-- name    : BlackwellDiscreteDP_Stationary_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:45:28.994608+00:00
-- url     : https://prove2.me/theorems/cc2a2e79-50db-4a9a-b1e6-af3f45d6f9e2
-- title:
--   Blackwell's finite decision model (§2): income i(s,a), law q(s'|s,a), policies, r(f), Q(f), Q_n(π), V_β(π), L(f), G(s,f), β-optimal and optimal
-- statement:
--   This file sets up the model of Blackwell's *Discrete Dynamic Programming* (1962), §1–§2, and the two optimality notions of §3 and §4.
--
--   **The model.** There are finitely many states $s$ and a finite set $A$ of actions, every action being available in every state. Choosing action $a$ in state $s$ yields an immediate **income** $i(s,a)\in\mathbb R$ (of either sign) and moves the system to state $s'$ with probability $q(s'\mid s,a)$, where $q(\cdot\mid s,a)$ is a probability vector.
--
--   **Policies.** Let $F$ be the finite set of functions $f$ from states to actions (decision rules). A **policy** is a sequence $\pi=\{f_n,\ n=1,2,\dots\}$ of elements of $F$: on day $n$, in state $s$, the action $f_n(s)$ is taken. For $g_1,\dots,g_N\in F$ and a policy $\pi$, $(g_1,\dots,g_N,\pi)$ is the policy that uses $g_1,\dots,g_N$ on the first $N$ days and then follows $\pi$; $g^{(N)},\pi$ uses $g$ on the first $N$ days and then $\pi$; $g^{(\infty)}$ uses $g$ every day (a **stationary** policy); $T\pi=\{f_{n+1}\}$ is the shifted policy.
--
--   **Returns.** For $f\in F$, $r(f)$ is the column vector with entries $i(s,f(s))$ and $Q(f)$ the Markov matrix with entries $q(s'\mid s,f(s))$. For a policy $\pi$, $Q_0(\pi)=I$ and $Q_n(\pi)=Q(f_1)Q(f_2)\cdots Q(f_n)$ (an ordered matrix product). For a discount factor $0\le\beta<1$ the **total expected return** of $\pi$ is the vector
--
--   $$V_\beta(\pi)=\sum_{n=0}^{\infty}\beta^n Q_n(\pi)\,r(f_{n+1}),$$
--
--   whose $s$th coordinate is the expected discounted income when starting in state $s$. The transformation $L(f)$ maps a vector $w$ to $L(f)w=r(f)+\beta Q(f)w$.
--
--   **Optimality.** Vectors are compared coordinatewise. A policy $\pi^*$ is **$\beta$-optimal** (Blackwell's "optimal" of §3) if $V_\beta(\pi^*)\ge V_\beta(\pi)$ for every policy $\pi$. A policy is **optimal** in the sense of §4 if it is $\beta$-optimal for all $\beta$ sufficiently near $1$, i.e. there is $\beta_0<1$ such that it is $\beta$-optimal for every $\beta\in(\beta_0,1)$. For $f\in F$ and a state $s$, $G(s,f)$ is the set of actions $a$ with
--
--   $$i(s,a)+\beta\,p(s,a)\,V_\beta(f^{(\infty)})>V_{\beta,s}(f^{(\infty)}),$$
--
--   where $p(s,a)$ is the row vector $(q(s'\mid s,a))_{s'}$ and $V_{\beta,s}$ denotes the $s$th coordinate.
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note.** States and actions are types; finiteness and nonemptiness are hypotheses of the theorems. The law of motion is a field `law s a s'` $=q(s'\mid s,a)$ whose stochasticity is the published predicate `IsTransitionKernel`. Policies are sequences indexed from $0$: `π 0` is $f_1$, so $V_\beta(\pi)=\sum_n\beta^nQ_n(\pi)r(\pi\,n)$ with $Q_n(\pi)=Q(\pi\,0)\cdots Q(\pi\,(n-1))$. The infinite sum is Lean's `tsum`, which is the genuine sum for $0\le\beta<1$ (the series converges absolutely); every theorem assumes $0\le\beta<1$ wherever $V_\beta$ appears at a fixed $\beta$. Blackwell defines §4 optimality as $V_\beta(\pi)=U(\beta)$ with $U(\beta)$ the return of a $\beta$-optimal policy; this is the same as $\beta$-optimality of $\pi$, so no supremum over policies is used. The strict order $w_1>w_2$ ("$w_1\ge w_2$ and $w_1\ne w_2$") is written out in each statement that uses it.
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, pp. 719–721, §2, §3 (G(s, f) from Theorem 3) and the opening of §4

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel

namespace BlackwellDiscreteDP.Stationary

/-- Blackwell's finite decision model (Blackwell, *Discrete Dynamic Programming*,
Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, §1–§2, p. 719).

States form the finite type `St` (Blackwell's `1, …, S`) and actions the finite type `Act`
(Blackwell's finite set `A`); every action is available in every state. `income s a` is the
immediate income `i(s, a)` (a real number of either sign) and `law s a s'` is the transition
probability `q(s' | s, a)`, which for each `(s, a)` is a probability vector in `s'`.

**Formalization Note.** The stochasticity of the law of motion is the published predicate
`FoundationsML.ReinforcementLearning.IsTransitionKernel` (`0 ≤ q(s'|s,a)` and
`∑_{s'} q(s'|s,a) = 1`), with the same argument order `law s a s' = q(s' | s, a)`. -/
structure Model (St Act : Type) [Fintype St] where
  /-- The immediate income `i(s, a)`. -/
  income : St → Act → ℝ
  /-- The law of motion: `law s a s' = q(s' | s, a)`. -/
  law : St → Act → St → ℝ
  /-- For every `(s, a)`, `q(· | s, a)` is a probability vector. -/
  law_kernel : FoundationsML.ReinforcementLearning.IsTransitionKernel law

/-- A policy `π = {f_n, n = 1, 2, ⋯}` (p. 719): a sequence of decision rules `f_n ∈ F`, where
`F` is the set of functions from states to actions.

**Formalization Note.** The sequence is indexed from `0`: `π 0` is Blackwell's `f₁` and
`π n` is `f_{n+1}`. -/
abbrev Policy (St Act : Type) : Type := ℕ → St → Act

/-- The policy `(f, π)` (p. 719, the case `N = 1` of `(g₁, ⋯, g_N, π)`): use `f` on the first
day, then follow `π` from the second day on (`h₁ = f`, `h_n = f_{n−1}` for `n > 1`). -/
def Policy.cons {St Act : Type} (f : St → Act) (π : Policy St Act) : Policy St Act :=
  fun n => Nat.casesOn n f (fun m => π m)

/-- The policy `(g₁, ⋯, g_N, π)` (p. 719): `h_n = g_n` for `1 ≤ n ≤ N`, `h_n = f_{n−N}` for
`n > N`. The list `[g₁, …, g_N]` is prepended to `π`. -/
def Policy.prepend {St Act : Type} (gs : List (St → Act)) (π : Policy St Act) :
    Policy St Act :=
  gs.foldr Policy.cons π

/-- The policy `g^(N), π` (p. 719): `h_n = g` for `1 ≤ n ≤ N`, `h_n = f_{n−N}` for `n > N`. -/
def Policy.repeatThen {St Act : Type} (g : St → Act) (N : ℕ) (π : Policy St Act) :
    Policy St Act :=
  fun n => if n < N then g else π (n - N)

/-- The stationary policy `g^(∞)` (p. 719): `h_n = g` for all `n`. -/
def stationary {St Act : Type} (g : St → Act) : Policy St Act :=
  fun _ => g

/-- The shifted policy `Tπ` (p. 719): `h_n = f_{n+1}`. -/
def Policy.shift {St Act : Type} (π : Policy St Act) : Policy St Act :=
  fun n => π (n + 1)

namespace Model

variable {St Act : Type} [Fintype St]

/-- `r(f)` (p. 719): the `S × 1` income vector whose `s`th element is `i(s, f(s))`. -/
def r (M : Model St Act) (f : St → Act) : St → ℝ :=
  fun s => M.income s (f s)

/-- `Q(f)` (p. 719): the `S × S` Markov matrix whose `(s, s')` element is `q(s' | s, f(s))`. -/
def Q (M : Model St Act) (f : St → Act) : Matrix St St ℝ :=
  Matrix.of fun s s' => M.law s (f s) s'

/-- `Q_n(π) = Q(f₁) Q(f₂) ⋯ Q(f_n)` (p. 719), with `Q₀(π) = I` (p. 720). The product is the
ordered matrix product: `Q_{n+1}(π) = Q_n(π) Q(f_{n+1})`, and `f_{n+1}` is `π n`. -/
def Qn [DecidableEq St] (M : Model St Act) (π : Policy St Act) : ℕ → Matrix St St ℝ
  | 0 => 1
  | n + 1 => Qn M π n * M.Q (π n)

/-- The total expected discounted return of `π` (p. 719),
`V_β(π) = ∑_{n=0}^∞ βⁿ Q_n(π) r(f_{n+1})`, a vector indexed by the initial state.

**Formalization Note.** The sum is the `tsum` in `St → ℝ`. Blackwell takes `0 ≤ β < 1`, and every
statement using `V` assumes this; then the entries of `Q_n(π)` lie in `[0, 1]`, `r` is bounded,
and the series converges absolutely, so the `tsum` is the genuine sum (it would be `0` only for a
non-summable series, which does not occur for `0 ≤ β < 1`). -/
noncomputable def V [DecidableEq St] (M : Model St Act) (β : ℝ) (π : Policy St Act) : St → ℝ :=
  ∑' n : ℕ, β ^ n • (M.Qn π n).mulVec (M.r (π n))

/-- The transformation `L(f)` (p. 720): `L(f)w = r(f) + βQ(f)w` for an `S × 1` vector `w`. -/
def L (M : Model St Act) (β : ℝ) (f : St → Act) (w : St → ℝ) : St → ℝ :=
  M.r f + β • (M.Q f).mulVec w

/-- `π*` is optimal in the sense of §3 (p. 720), here called **β-optimal** as in §4 (p. 721):
`π* ≧ π` for all policies `π`, i.e. `V_β(π*) ≧ V_β(π)` coordinatewise for every policy `π`
(deterministic Markov, possibly time-dependent). -/
def IsBetaOptimal [DecidableEq St] (M : Model St Act) (β : ℝ) (πstar : Policy St Act) : Prop :=
  ∀ π : Policy St Act, M.V β π ≤ M.V β πstar

/-- The set `G(s, f)` of Theorem 3 (p. 720): all actions `a` with
`i(s, a) + β p(s, a) V(f^(∞)) > V_s(f^(∞))`, where `p(s, a)` is the row vector
`(q(s' | s, a))_{s'}` and `V_s(f^(∞))` is the `s`th coordinate of `V_β(f^(∞))`. -/
def G [DecidableEq St] (M : Model St Act) (β : ℝ) (f : St → Act) (s : St) : Set Act :=
  {a | M.V β (stationary f) s <
      M.income s a + β * ∑ s' : St, M.law s a s' * M.V β (stationary f) s'}

/-- A policy is **optimal** in the sense of §4 (p. 721): it is β-optimal for all `β`
sufficiently near `1`, i.e. there is `β₀ < 1` such that it is β-optimal for every
`β ∈ (β₀, 1)`. (Today this is called Blackwell optimality.)

**Formalization Note.** This is a different notion from the §3 "optimal", which is
`IsBetaOptimal β` at one fixed `β`. Blackwell phrases it as `V_β(π) = U(β)` for all `β`
sufficiently near `1`, where `U(β)` is the return of a β-optimal policy; since `U(β) ≧ V_β(π')`
for every `π'`, that is the same as `IsBetaOptimal β π`, and no supremum over policies is
needed. -/
def IsOptimal [DecidableEq St] (M : Model St Act) (π : Policy St Act) : Prop :=
  ∃ β₀ : ℝ, β₀ < 1 ∧ ∀ β : ℝ, β₀ < β → β < 1 → M.IsBetaOptimal β π

end Model

end BlackwellDiscreteDP.Stationary



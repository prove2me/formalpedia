-- Prove2me | Definitions.Def_BlackwellDiscreteDP_NearOne_Model
-- name    : BlackwellDiscreteDP_NearOne_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:46:12.578893+00:00
-- url     : https://prove2.me/theorems/a22c0b4c-a493-4722-885d-c2fcf58a5baa
-- title:
--   Finite decision model (§2): income i(s,a), law of motion q(s'|s,a), policies, r(f), Q(f), V_β(π); β-optimal, optimal and nearly optimal policies
-- statement:
--   This file sets up the finite discounted decision model of Blackwell's *Discrete Dynamic Programming* (1962), §2, and the optimality notions of §3 and §4.
--
--   **The model.** There is a finite nonempty set $S$ of states and a finite nonempty set $A$ of actions, every action being available in every state. Choosing action $a$ in state $s$ yields an immediate income $i(s,a)\in\mathbb R$ (of any sign) and moves the system to state $s'$ with probability $q(s'\mid s,a)$, where $q(\cdot\mid s,a)$ is a probability vector. $F$ is the finite set of decision rules $f:S\to A$.
--
--   **Policies.** A policy is a sequence $\pi=\{f_n,\ n=1,2,\dots\}$ of decision rules, $f_n$ being used on day $n$. $(g,\pi)$ uses $g$ on the first day and then follows $\pi$; $f^{(\infty)}$ is the stationary policy using $f$ every day.
--
--   **Returns.** For $f\in F$, $r(f)$ is the column vector with $s$th entry $i(s,f(s))$ and $Q(f)$ the Markov matrix with $(s,s')$ entry $q(s'\mid s,f(s))$. With $Q_0(\pi)=I$ and $Q_n(\pi)=Q(f_1)\cdots Q(f_n)$, the expected total discounted return of $\pi$ is the vector
--   $$V_\beta(\pi)=\sum_{n=0}^\infty \beta^n\,Q_n(\pi)\,r(f_{n+1}),\qquad 0\le\beta<1.$$
--   The row vector $p(s,a)$ has $s'$th coordinate $q(s'\mid s,a)$.
--
--   **Orders and optimality.** Vectors are compared coordinatewise: $w_1\ge w_2$ if every coordinate is at least as large, and $w_1>w_2$ if $w_1\ge w_2$ and $w_1\ne w_2$. A policy $\pi$ is
--   1. **β-optimal** if $V_\beta(\pi)\ge V_\beta(\pi')$ for every policy $\pi'$ (the "optimal" of §3);
--   2. **optimal** (§4) if it is β-optimal for all β sufficiently near $1$, i.e. for all $\beta$ in some interval $(\beta_0,1)$;
--   3. **nearly optimal** (§4) if $U(\beta)-V_\beta(\pi)\to0$ as $\beta\to1$, where $U(\beta)$ is the return of a β-optimal policy.
--
--   Finally, Theorem 3's set $G_\beta(s,f)$ consists of the actions $a$ with $i(s,a)+\beta\,p(s,a)V_\beta(f^{(\infty)})>V_\beta(f^{(\infty)})_s$.
--
--   These are the objects every result of the paper is stated in.
--
--   **Formalization Note** Policy indices start at $0$: `π 0` is $f_1$. $V_\beta$ is a real `tsum`; it converges absolutely for $0\le\beta<1$. "Nearly optimal" is stated without $U$: for every $\varepsilon>0$ there is $\beta_0<1$ such that for all $\beta\in(\beta_0,1)$, all policies $\pi'$ and all states $s$, $V_\beta(\pi')_s\le V_\beta(\pi)_s+\varepsilon$. Because a β-optimal policy exists for every $\beta\in[0,1)$ (the Corollary of §3) and dominates every policy, this is equivalent to $U(\beta)-V_\beta(\pi)\to0$. The two meanings of "optimal" have different names (`IsBetaOptimal`, `IsOptimal`), and Theorem 3's set $G_\beta$ is named `betaImprovementSet` to distinguish it from the §4 set $G(s,f)$.
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, pp. 719–721, §2, §3 (Theorem 3), §4 (definitions of optimal and nearly optimal)

import Mathlib
open Filter Topology Matrix

namespace BlackwellDiscreteDP.NearOne

/-- Blackwell's finite decision model (§2): a finite set `St` of states, a finite set `Act` of
actions (every action available in every state), an immediate income `i(s, a)` of any sign, and
a law of motion `q(s' | s, a)` (here `q s a s'`), a probability vector over `s'` for every
`(s, a)`.

Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593, p. 719, §1–§2.

**Formalization Note.** Finiteness and nonemptiness of `St` and `Act` are typeclass hypotheses
of the theorems (`[Fintype St] [Nonempty St] [Fintype Act] [Nonempty Act]`). -/
structure Model (St Act : Type*) [Fintype St] where
  /-- immediate income `i(s, a)` -/
  i : St → Act → ℝ
  /-- law of motion: `q s a s'` is `q(s' | s, a)` -/
  q : St → Act → St → ℝ
  q_nonneg : ∀ s a s', 0 ≤ q s a s'
  q_sum_one : ∀ s a, ∑ s', q s a s' = 1

variable {St Act : Type*} [Fintype St] [DecidableEq St]

/-- A **policy** `π = {f_n, n = 1, 2, ⋯}`: a sequence of decision rules `f_n : St → Act`
(deterministic, Markov, possibly time-dependent).

Blackwell (1962), p. 719, §2.

**Formalization Note.** Indices start at `0`: `π 0` is the paper's `f₁`, `π n` is `f_{n+1}`. -/
abbrev Policy (St Act : Type*) := ℕ → St → Act

/-- The policy `(g, π)`: use `g` on the first day, then follow `π`. Blackwell (1962), p. 719. -/
def Policy.cons (g : St → Act) (π : Policy St Act) : Policy St Act
  | 0 => g
  | n + 1 => π n

/-- The stationary policy `f^(∞)`: use `f` every day. Blackwell (1962), p. 719. -/
def Policy.stationary (f : St → Act) : Policy St Act := fun _ => f

namespace Model

variable (M : Model St Act)

/-- `r(f)`: the column vector whose `s`th element is `i(s, f(s))`. Blackwell (1962), p. 719. -/
def r (f : St → Act) : St → ℝ := fun s => M.i s (f s)

/-- `Q(f)`: the `S × S` Markov matrix whose `(s, s')` element is `q(s' | s, f(s))`.
Blackwell (1962), p. 719. -/
def Q (f : St → Act) : Matrix St St ℝ := Matrix.of fun s s' => M.q s (f s) s'

/-- `Q_n(π) = Q(f₁)Q(f₂)⋯Q(f_n)` (ordered product), `Q_0(π) = I`. Blackwell (1962), pp. 719–720.

With the index shift `π 0 = f₁`: `Q_{n+1}(π) = Q_n(π) Q(π n)`. -/
def Qn (π : Policy St Act) : ℕ → Matrix St St ℝ
  | 0 => 1
  | n + 1 => Qn π n * M.Q (π n)

/-- The expected total discounted return `V_β(π) = ∑_{n=0}^∞ βⁿ Q_n(π) r(f_{n+1})`, a vector
indexed by the initial state. Blackwell (1962), p. 719, §2 (and §4, p. 721, for the notation
`V_β`).

**Formalization Note.** A real `tsum` in `St → ℝ`. For `0 ≤ β < 1` the series converges
absolutely (the entries of `Q_n(π)` lie in `[0, 1]` and `r` is bounded), so the value is the
paper's; outside that range it is not used by any statement except through limits `β → 1⁻`. -/
noncomputable def V (β : ℝ) (π : Policy St Act) : St → ℝ :=
  ∑' n : ℕ, β ^ n • (M.Qn π n *ᵥ M.r (π n))

/-- `π` is **β-optimal** (the §3 notion "optimal", β fixed): `V_β(π) ≧ V_β(π')`
coordinatewise for every policy `π'`. Blackwell (1962), p. 720, §2 and p. 721, §4. -/
def IsBetaOptimal (β : ℝ) (π : Policy St Act) : Prop :=
  ∀ π' : Policy St Act, M.V β π' ≤ M.V β π

/-- `π` is **optimal in the sense of §4** (today: Blackwell optimal): it is β-optimal for all β
sufficiently near 1, i.e. there is `β₀ < 1` such that `π` is β-optimal for every
`β ∈ (β₀, 1)`. Blackwell (1962), p. 721, §4.

**Formalization Note.** This is a different notion from the §3 "optimal" (`IsBetaOptimal`). -/
def IsOptimal (π : Policy St Act) : Prop :=
  ∃ β₀ < (1 : ℝ), ∀ β : ℝ, β₀ < β → β < 1 → M.IsBetaOptimal β π

/-- `π` is **nearly optimal** (§4): `U(β) − V_β(π) → 0` as `β → 1`, where `U(β)` is the return
of a β-optimal policy. Blackwell (1962), p. 721, §4.

**Formalization Note.** Encoded without `U`: for every `ε > 0` there is `β₀ < 1` such that for
every `β ∈ (β₀, 1)`, every policy `π'` and every state `s`, `V_β(π')_s ≤ V_β(π)_s + ε`. Since a
β-optimal policy exists for each `β ∈ [0, 1)` (the Corollary of §3) and `U(β) ≧ V_β(π)`, this is
equivalent to the paper's definition. -/
def IsNearlyOptimal (π : Policy St Act) : Prop :=
  ∀ ε > (0 : ℝ), ∃ β₀ < (1 : ℝ), ∀ β : ℝ, β₀ < β → β < 1 →
    ∀ π' : Policy St Act, ∀ s, M.V β π' s ≤ M.V β π s + ε

/-- `p(s, a) w = ∑_{s'} q(s' | s, a) w_{s'}`: the `1 × S` row vector `p(s, a)` (whose `s'`th
coordinate is `q(s' | s, a)`) applied to a column vector `w`. Blackwell (1962), p. 721,
Theorem 3. -/
def pDot (s : St) (a : Act) (w : St → ℝ) : ℝ := ∑ s', M.q s a s' * w s'

/-- Theorem 3's set `G(s, f)` (depends on `β`): the actions `a` with
`i(s, a) + β p(s, a) V(f^(∞)) > V_s(f^(∞))`.
Blackwell (1962), pp. 720–721, Theorem 3.

**Formalization Note.** Named `betaImprovementSet` to distinguish it from the §4 set `G(s, f)`
of Theorem 4(b) (`gainBiasImprovementSet`), which has no `β`. -/
def betaImprovementSet (β : ℝ) (f : St → Act) (s : St) : Set Act :=
  {a | M.i s a + β * M.pDot s a (M.V β (Policy.stationary f)) > M.V β (Policy.stationary f) s}

end Model

/-- The strict vector order of §2: `w₁ > w₂` iff `w₁ ≧ w₂` coordinatewise and `w₁ ≠ w₂`
(not coordinatewise strict). Blackwell (1962), p. 720. -/
def VecGt (w₁ w₂ : St → ℝ) : Prop := w₂ ≤ w₁ ∧ w₁ ≠ w₂

end BlackwellDiscreteDP.NearOne



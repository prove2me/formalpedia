-- Prove2me | Definitions.Def_InfoRelax_IdealPenalty_RecursiveModel
-- name    : InfoRelax_IdealPenalty_RecursiveModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:11.224583+00:00
-- url     : https://prove2.me/theorems/d6b1c9b7-75a2-441c-aa09-4b805df85a72
-- title:
--   A DP in recursive form and its value functions $V_t$ (eq. (2))
-- statement:
--   This file fixes the recursive (Bellman) form of a finite-horizon stochastic dynamic program, as in §2.1 of Brown, Smith and Sun.
--
--   A **recursive DP** consists of
--   1. a natural filtration $\mathbb F=(\mathcal F_0,\dots,\mathcal F_T)$;
--   2. feasible-action sets $A_t(a_0,\dots,a_{t-1})\subseteq X$;
--   3. period rewards $r_t(a_0,\dots,a_t)(\omega)$.
--
--   Its standing assumptions are: $\mathcal F_0=\{\emptyset,\Omega\}$; each $A_t$ depends only on $a_0,\dots,a_{t-1}$ and is nonempty; each $r_t(a)$ is $\mathcal F_t$-measurable and depends only on $a_0,\dots,a_t$; and the period rewards are bounded by a single constant. The feasible sequences are $A=\{a: a_t\in A_t(a_0,\dots,a_{t-1})\ \text{for all }t\}$ and the total reward is $r(a,\omega)=\sum_{t=0}^T r_t(a,\omega)$.
--
--   For per-period rewards $f_t$ and a filtration $\mathbb G$, the **backward recursion** is $W_{T+1}=0$ and, for $t=0,\dots,T$,
--   $$W_t(a_0,\dots,a_{t-1})=\sup_{a_t\in A_t(a_0,\dots,a_{t-1})}\big\{f_t(a_0,\dots,a_t)+\mathbb E[W_{t+1}(a_0,\dots,a_t)\mid\mathcal G_t]\big\}.$$
--   With $f_t=r_t$ and $\mathbb G=\mathbb F$ this is the primal value function $V_t$ of eq. (2):
--   $$V_t(a_0,\dots,a_{t-1})=\sup_{a_t\in A_t(a_0,\dots,a_{t-1})}\big\{r_t(a_0,\dots,a_t)+\mathbb E[V_{t+1}(a_0,\dots,a_t)\mid\mathcal F_t]\big\}.\qquad(2)$$
--
--   The same recursion with penalized rewards and a relaxed filtration gives the dual value functions of eq. (10).
--
--   **Formalization Note** Functions of the first $t+1$ actions are written on full action sequences; the period-$t$ action is inserted with `Function.update`. The time index of the recursion is a natural number and $W_t=0$ for all $t>T$. Conditional expectations are Mathlib's `condExp`, a fixed version determined almost everywhere, so identities between value functions are almost sure. The supremum is the real supremum over the nonempty feasible set; where a version of a conditional expectation is unbounded in the action (a null set) it takes Lean's default value $0$. Pinned regularity, used by the theorems: a countable action type with the discrete $\sigma$-algebra, and bounded period rewards. Endnote 1 (p. 16): action sets do not depend on $\omega$.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 3, §2.1, recursive form and eq. (2); p. 16, endnote 1

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework

open MeasureTheory

namespace InfoRelax.IdealPenalty

/-!
# The recursive setting of Brown, Smith & Sun (2010), §2.1, and the value functions (2)

Brown, Smith & Sun, *Information Relaxations and Duality in Stochastic Dynamic Programs*,
Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 3, the paragraph
"It is instructive to write the primal DP (1) in the standard Bellman-style recursive form"
and eq. (2); endnote 1, p. 16.

A dynamic program in recursive form has a natural filtration `𝔽`, feasible-action sets
`A_t(a_0, …, a_{t−1})` and period rewards `r_t(a_0, …, a_t)`. The feasible sequences are
`A = {a : a_t ∈ A_t(a_0, …, a_{t−1}) for all t}` and the total reward is `r = ∑_t r_t`.

`bellman μ 𝔾 Afeas f` is the backward recursion of eq. (2) for per-period rewards `f` and
information filtration `𝔾`:
`W_{T+1} = 0`, and for `t = 0, …, T`,
`W_t(a) = sup_{x ∈ A_t(a)} { f_t(a_0, …, a_{t−1}, x) + 𝔼[W_{t+1}(a_0, …, a_{t−1}, x) | 𝒢_t] }`.
The primal value functions of (2) are `valueFn M μ = bellman μ M.𝔽 M.Afeas M.rt`.

**Formalization Note.**
* Functions of "the first `t + 1` actions" are written on full sequences `a : Fin (T + 1) → X`;
  `Function.update a t x` puts the period-`t` action `x` in place, and the regularity predicate
  `Valid` requires that `A_t` depends only on `a_0, …, a_{t−1}` and `r_t` only on `a_0, …, a_t`.
  Hence `W_t(a)` depends only on `a_0, …, a_{t−1}`.
* The time index of `bellman` is a natural number; `W_t = 0` for every `t > T`, so
  `W_{T+1} = 0` is the page's terminal condition.
* Conditional expectations are Mathlib's `μ[· | m]`, a fixed version of the conditional
  expectation; it is determined only almost everywhere, so identities between value functions
  hold almost surely.
* The supremum over `x ∈ A_t(a)` is the real `⨆` over the subtype. `Valid` makes the set nonempty
  and the family bounded almost everywhere; on the exceptional null set (where a version of a
  conditional expectation is unbounded in `x`) the real supremum takes Lean's default value `0`.
  With countably many action sequences (countable `X`) this happens only on a null set.
* Pinned regularity of the recursive setting (the paper asserts on p. 3 that the supremum in (2)
  is `𝓕_t`-measurable, which holds for countable action sets): `X` is countable with the discrete
  σ-algebra, and the period rewards are bounded by one constant.
* Endnote 1 (p. 16): the action sets do not depend on the outcome `ω`.
-/

variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] {T : ℕ}

/-- The data of a DP in recursive form (p. 3): the natural filtration `𝔽`, the feasible-action
sets `Afeas t a = A_t(a_0, …, a_{t−1})`, and the period rewards `rt t a ω = r_t(a_0, …, a_t)(ω)`. -/
structure RecursiveDP (Ω X : Type*) [mΩ : MeasurableSpace Ω] (T : ℕ) where
  /-- The natural filtration `𝔽 = (𝓕_0, …, 𝓕_T)`. -/
  𝔽 : Filtration (Fin (T + 1)) mΩ
  /-- `Afeas t a = A_t(a_0, …, a_{t−1})`, the period-`t` actions feasible after `a_0, …, a_{t−1}`. -/
  Afeas : Fin (T + 1) → (Fin (T + 1) → X) → Set X
  /-- `rt t a ω = r_t(a_0, …, a_t)(ω)`, the period-`t` reward. -/
  rt : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ

namespace RecursiveDP

/-- The standing assumptions of the recursive setting (§2.1, pp. 2–3):
1. `𝓕_0 = {∅, Ω}`;
2. `A_t` depends only on `a_0, …, a_{t−1}` and is nonempty;
3. `r_t(a)` is `𝓕_t`-measurable for each `a` and depends only on `a_0, …, a_t`;
4. (pinned) the period rewards are bounded by a single constant. -/
def Valid (M : RecursiveDP Ω X T) : Prop :=
  M.𝔽 0 = ⊥ ∧
  (∀ t a a', (∀ s, s < t → a s = a' s) → M.Afeas t a = M.Afeas t a') ∧
  (∀ t a, (M.Afeas t a).Nonempty) ∧
  (∀ t a, Measurable[M.𝔽 t] (M.rt t a)) ∧
  (∀ t a a', (∀ s, s ≤ t → a s = a' s) → M.rt t a = M.rt t a') ∧
  (∃ C : ℝ, ∀ t a ω, |M.rt t a ω| ≤ C)

/-- The feasible action sequences `A = {a : a_t ∈ A_t(a_0, …, a_{t−1}) for all t}`. -/
def A (M : RecursiveDP Ω X T) : Set (Fin (T + 1) → X) :=
  {a | ∀ t, a t ∈ M.Afeas t a}

/-- The total reward `r(a, ω) = ∑_{t=0}^T r_t(a, ω)` (p. 3). -/
def r (M : RecursiveDP Ω X T) (a : Fin (T + 1) → X) (ω : Ω) : ℝ :=
  ∑ t, M.rt t a ω

end RecursiveDP

variable [DecidableEq X]

/-- The backward recursion of eq. (2) (and of eq. (10)) for per-period rewards `f`, feasible
sets `Afeas`, and information filtration `𝔾`: `bellman … t a = 0` for `t > T`, and for `t ≤ T`
`bellman … t a ω = ⨆ x ∈ A_t(a), f_t(a[t ↦ x])(ω) + 𝔼[bellman … (t+1) (a[t ↦ x]) | 𝒢_t](ω)`. -/
noncomputable def bellman (μ : Measure Ω) (𝔾 : Filtration (Fin (T + 1)) mΩ)
    (Afeas : Fin (T + 1) → (Fin (T + 1) → X) → Set X)
    (f : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) : ℕ → (Fin (T + 1) → X) → Ω → ℝ
  | t, a =>
    if h : t ≤ T then
      fun ω => ⨆ x : Afeas ⟨t, Nat.lt_succ_of_le h⟩ a,
        f ⟨t, Nat.lt_succ_of_le h⟩ (Function.update a ⟨t, Nat.lt_succ_of_le h⟩ x.1) ω +
          μ[bellman μ 𝔾 Afeas f (t + 1) (Function.update a ⟨t, Nat.lt_succ_of_le h⟩ x.1) |
            𝔾 ⟨t, Nat.lt_succ_of_le h⟩] ω
    else 0
termination_by t => T + 1 - t
decreasing_by omega

/-- The primal value functions `V_t(a_0, …, a_{t−1})` of eq. (2), p. 3, with `V_{T+1} = 0`. -/
noncomputable def valueFn (M : RecursiveDP Ω X T) (μ : Measure Ω) :
    ℕ → (Fin (T + 1) → X) → Ω → ℝ :=
  bellman μ M.𝔽 M.Afeas M.rt

end InfoRelax.IdealPenalty



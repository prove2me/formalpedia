-- Prove2me | Definitions.Def_InfoRelax_RelaxOrder_RecursiveModel
-- name    : InfoRelax_RelaxOrder_RecursiveModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:05.879047+00:00
-- url     : https://prove2.me/theorems/c0127081-98c1-4fb7-821b-119696e240f1
-- title:
--   A dynamic program in recursive form and the backward recursion (2) (§2.1)
-- statement:
--   This file fixes the recursive form of a finite-horizon dynamic program (Brown, Smith and Sun, §2.1, p. 3).
--
--   A **dynamic program in recursive form** consists of
--
--   1. a natural filtration $\mathbb F=(\mathcal F_0,\dots,\mathcal F_T)$ with $\mathcal F_0=\{\emptyset,\Omega\}$;
--   2. feasible-action sets $A_t(a_0,\dots,a_{t-1})\subseteq X$, nonempty and depending only on the earlier actions (not on the outcome $\omega$, endnote 1);
--   3. period rewards $r_t(a_0,\dots,a_t)(\omega)$, each $\mathcal F_t$-measurable, depending only on the first $t+1$ actions, and bounded by one constant.
--
--   The feasible sequences are $A=\{a:\ a_t\in A_t(a_0,\dots,a_{t-1})\text{ for all }t\}$ and the total reward is $r(a,\omega)=\sum_{t=0}^T r_t(a,\omega)$.
--
--   For per-period rewards $f_t$ and a filtration $\mathbb G$, the **backward recursion** is $W_{T+1}=0$ and, for $t=0,\dots,T$,
--   $$W_t(a_0,\dots,a_{t-1})=\sup_{a_t\in A_t(a_0,\dots,a_{t-1})}\Big\{f_t(a_0,\dots,a_t)+\mathbb E\big[W_{t+1}(a_0,\dots,a_t)\,\big|\,\mathcal G_t\big]\Big\}.$$
--   With $f=r$ and $\mathbb G=\mathbb F$ it is the Bellman recursion (2); with the penalized rewards $r_t-z_t$ and a relaxation $\mathbb G$ it is the dual recursion (10).
--
--   **Formalization Note** Functions of the first $t$ actions are written on full sequences, with the period-$t$ action inserted by `Function.update`. The time index is a natural number and $W_t=0$ for $t>T$. Conditional expectations are Mathlib's fixed versions, determined almost surely; the supremum is the real supremum over the feasible set, which takes Lean's default value $0$ only on the null set where a version is unbounded. The bound on the rewards is a pinned regularity assumption; the theorems using this file also assume a countable action set, under which the supremum in (2) is measurable, as the paper asserts.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 3, §2.1, recursive form and eq. (2); endnote 1, p. 16

import Mathlib
import Definitions.Def_InfoRelax_RelaxOrder_Framework

open MeasureTheory

namespace InfoRelax.RelaxOrder

/-!
# The recursive setting of Brown, Smith & Sun (2010), §2.1, and the backward recursion (2)

Brown, Smith & Sun, *Information Relaxations and Duality in Stochastic Dynamic Programs*,
Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 3, the paragraph
"It is instructive to write the primal DP (1) in the standard Bellman-style recursive form"
and eq. (2); endnote 1, p. 16.

A dynamic program in recursive form has a natural filtration `𝔽`, feasible-action sets
`A_t(a_0, …, a_{t−1})` and period rewards `r_t(a_0, …, a_t)`. The feasible sequences are
`A = {a : a_t ∈ A_t(a_0, …, a_{t−1}) for all t}` and the total reward is `r = ∑_t r_t`.

`bellman μ 𝔾 Afeas f` is the backward recursion of eq. (2) for per-period rewards `f` and
information filtration `𝔾`: `W_{T+1} = 0`, and for `t = 0, …, T`,
`W_t(a) = sup_{x ∈ A_t(a)} { f_t(a_0, …, a_{t−1}, x) + 𝔼[W_{t+1}(a_0, …, a_{t−1}, x) | 𝒢_t] }`.

**Formalization Note.**
* Functions of "the first `t + 1` actions" are written on full sequences `a : Fin (T + 1) → X`;
  `Function.update a t x` puts the period-`t` action `x` in place, and `Valid` requires that
  `A_t` depends only on `a_0, …, a_{t−1}` and `r_t` only on `a_0, …, a_t`.
* The time index of `bellman` is a natural number; `W_t = 0` for every `t > T`, so
  `W_{T+1} = 0` is the page's terminal condition.
* Conditional expectations are Mathlib's `μ[· | m]`, a fixed version of the conditional
  expectation; it is determined only almost everywhere.
* The supremum over `x ∈ A_t(a)` is the real `⨆` over the subtype. `Valid` makes the set nonempty
  and (with bounded data) the family is bounded almost everywhere; on the exceptional null set
  where a version is unbounded in `x`, the real supremum takes Lean's default value `0`.
* Pinned regularity of the recursive setting (the paper asserts on p. 3 that the supremum in (2)
  is `𝓕_t`-measurable, which holds for countable action sets): theorems using this file assume
  `X` countable with the discrete σ-algebra; `Valid` bounds the period rewards by one constant.
* Endnote 1 (p. 16): the action sets do not depend on the outcome `ω`.
* Identical in content to mission 1's `InfoRelax.IdealPenalty.RecursiveModel` (drafts cannot
  import drafts).
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

end InfoRelax.RelaxOrder



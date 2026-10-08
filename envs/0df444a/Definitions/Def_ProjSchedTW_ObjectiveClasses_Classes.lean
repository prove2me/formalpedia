-- Prove2me | Definitions.Def_ProjSchedTW_ObjectiveClasses_Classes
-- name    : ProjSchedTW_ObjectiveClasses_Classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:22:21.058152+00:00
-- url     : https://prove2.me/theorems/34f6f012-fba4-4322-9b4c-717541633fdd
-- title:
--   §2.4, §3.2, §3.3 — shifts, (quasi)active and (quasi)stable schedules, classes of objective functions, resource investment
-- statement:
--   This file defines the schedule classes and the classes of objective functions of §3.3, for a project as in the companion definition file ($V=\{0,\dots,n+1\}$, feasible region $\mathcal S$, induced order $O(S)$, equal-order sets $\mathcal S_T^{=}(O(S))$).
--
--   1. **Shifts** (Definitions 2.4.1, 2.4.2, 2.4.4, 3.2.2). A left-shift from $S$ to $S'$ means $S'\le S$ and $S'\ne S$. A global shift transforms a feasible schedule $S$ into a feasible schedule $S'\ne S$; it is order-preserving if moreover $O(S)\subseteq O(S')$. Two shifts from $S$ to $S'$ and $S''$ are opposite if $S''-S=\lambda(S'-S)$ for some $\lambda<0$.
--   2. **Schedule classes** (Definitions 2.4.6, 3.2.6). A feasible schedule $S$ is *active* if there is no global left-shift from $S$, *quasiactive* if there is no order-preserving left-shift from $S$, *stable* if there is no pair of opposite global shifts from $S$, and *quasistable* if there is no pair of opposite order-preserving shifts from $S$.
--   3. **Regular and quasiconcave functions** (§3.3.2, §3.3.6). A function $f$ is regular on a set $M$ if $S\le S'$ implies $f(S)\le f(S')$ for all $S,S'\in M$, and quasiconcave on $M$ if
--   $$f(\lambda S+(1-\lambda)S')\ \ge\ \min[f(S),f(S')]\qquad\text{for all } S,S'\in M,\ \lambda\in[0,1].$$
--   Class 1 (regular) and class 5 (quasiconcave) take $M=\mathbb R^{n+2}_{\ge 0}$.
--   4. **Lower semicontinuity** (Definition 3.3.3). $f$ is lower semicontinuous if $f(S)\le\liminf_{S'\to S}f(S')$ for all $S\in\mathbb R^{n+2}_{\ge 0}$, with $S'$ ranging over $\mathbb R^{n+2}_{\ge 0}$.
--   5. **Locally regular and locally quasiconcave functions** (Definitions 3.3.7, 3.3.11). $f$ is locally regular (class 6) if it is lower semicontinuous and regular on $\mathcal S_T^{=}(O(S))$ for each $S\in\mathcal S$; it is locally quasiconcave (class 7) if it is lower semicontinuous and quasiconcave on $\mathcal S_T^{=}(O(S))$ for each $S\in\mathcal S$.
--   6. **Resource investment** (§3.1, p. 203). With procurement costs $c_k$ per unit of resource $k$,
--   $$f(S)=\sum_{k\in\mathcal R}c_k\max_{t}r_k(S,t).$$
--
--   These are the objects of the mission's statements: each theorem pairs a class of objective functions with a class of schedules that is guaranteed to contain an optimal schedule.
--
--   **Formalization Note** Objective functions are total functions on $\mathbb R^{n+2}$; only their values on the nonnegative orthant enter the definitions. Lower semicontinuity is Mathlib's `LowerSemicontinuousOn` on the orthant. The peak $\max_t r_k(S,t)$ is taken over all $t\ge 0$ as a supremum in $\mathbb N$ of a nonempty finite set, so it is attained; for feasible schedules all activities lie in $[0,\bar d]$, so it equals the book's $\max_{0\le t\le\bar d}$.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, p. 39, Definitions 2.4.1, 2.4.2, 2.4.4; pp. 41–42, Definition 2.4.6; p. 207, Definition 3.2.2; p. 210, Definition 3.2.6; p. 203 (resource investment); p. 221 (regular); p. 225 (quasiconcave); p. 227, Definition 3.3.3; p. 230, Definition 3.3.7; p. 233, Definition 3.3.11

import Mathlib
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Project
import Definitions.Def_ProjSchedTW_ActiveSchedules_Shifts
import Definitions.Def_ProjSchedTW_StableSchedules_Shifts

namespace ProjSchedTW.ObjectiveClasses

variable {n : ℕ} {K : Type}

/-! ### Shifts and schedule classes (Definitions 2.4.1–2.4.4, 2.4.6, 3.2.2, 3.2.6) -/

/-- Definition 2.4.2 (p. 39): a global shift transforms a feasible schedule `S` into a feasible
schedule `S' ≠ S`. -/
def IsGlobalShift (P : Project n K) (S S' : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧ S' ∈ feasibleSet P ∧ S' ≠ S

/-- Definition 2.4.4 (p. 39): a shift between feasible schedules is order-preserving if
`O(S) ⊆ O(S')`. -/
def IsOrderPreservingShift (P : Project n K) (S S' : Fin (n + 2) → ℝ) : Prop :=
  IsGlobalShift P S S' ∧ scheduleOrder P S ⊆ scheduleOrder P S'

/-- Definition 2.4.6 (pp. 41–42): a feasible schedule is active if there is no global
left-shift from it (the set `AS`). -/
def IsActive (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧ ¬ ∃ S', IsGlobalShift P S S' ∧ ProjSchedTW.ActiveSchedules.IsLeftShift S S'

/-- Definition 2.4.6 (pp. 41–42): a feasible schedule is quasiactive if there is no
order-preserving left-shift from it (the set `QAS`). -/
def IsQuasiactive (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧ ¬ ∃ S', IsOrderPreservingShift P S S' ∧ ProjSchedTW.ActiveSchedules.IsLeftShift S S'

/-- Definition 3.2.6 (p. 210): a feasible schedule is stable if there is no pair of opposite
global shifts from it (the set `SS`). -/
def IsStable (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧
    ¬ ∃ S' S'', IsGlobalShift P S S' ∧ IsGlobalShift P S S'' ∧ ProjSchedTW.StableSchedules.AreOpposite S S' S''

/-- Definition 3.2.6 (p. 210): a feasible schedule is quasistable if there is no pair of
opposite order-preserving shifts from it (the set `QSS`). -/
def IsQuasistable (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧
    ¬ ∃ S' S'', IsOrderPreservingShift P S S' ∧ IsOrderPreservingShift P S S'' ∧
      ProjSchedTW.StableSchedules.AreOpposite S S' S''

/-! ### Classes of objective functions (§3.3) -/

/-- The nonnegative orthant `ℝ^{n+2}_{≥0}`, the domain of the objective functions of
Chapter 3. -/
def orthant (n : ℕ) : Set (Fin (n + 2) → ℝ) :=
  {S | ∀ i, 0 ≤ S i}

/-- §3.3.2 (p. 221), applied to a set `M`: `f` is regular (nondecreasing) on `M` if `S ≤ S'`
implies `f(S) ≤ f(S')` for all `S, S' ∈ M`. -/
def IsRegularOn (M : Set (Fin (n + 2) → ℝ)) (f : (Fin (n + 2) → ℝ) → ℝ) : Prop :=
  ∀ S ∈ M, ∀ S' ∈ M, S ≤ S' → f S ≤ f S'

/-- §3.3.6 (p. 225), applied to a set `M`: `f` is quasiconcave on `M` if
`f(λS + (1 − λ)S') ≥ min[f(S), f(S')]` for all `S, S' ∈ M` and `λ ∈ [0, 1]`. -/
def IsQuasiconcaveOn (M : Set (Fin (n + 2) → ℝ)) (f : (Fin (n + 2) → ℝ) → ℝ) : Prop :=
  ∀ S ∈ M, ∀ S' ∈ M, ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    min (f S) (f S') ≤ f (lam • S + (1 - lam) • S')

/-- §3.3.2 (p. 221): `f : ℝ^{n+2}_{≥0} → ℝ` is regular (class 1) if `S ≤ S'` implies
`f(S) ≤ f(S')` for all `S, S' ∈ ℝ^{n+2}_{≥0}`. -/
def IsRegular (f : (Fin (n + 2) → ℝ) → ℝ) : Prop :=
  IsRegularOn (orthant n) f

/-- §3.3.6 (p. 225): `f : ℝ^{n+2}_{≥0} → ℝ` is quasiconcave (class 5) if
`f(λS + (1 − λ)S') ≥ min[f(S), f(S')]` for all `S, S' ∈ ℝ^{n+2}_{≥0}` and `λ ∈ [0, 1]`. -/
def IsQuasiconcave (f : (Fin (n + 2) → ℝ) → ℝ) : Prop :=
  IsQuasiconcaveOn (orthant n) f

/-- Definition 3.3.3 (p. 227): `f : ℝ^{n+2}_{≥0} → ℝ` is lower semicontinuous if
`f(S) ≤ liminf_{S' → S} f(S')` for all `S ∈ ℝ^{n+2}_{≥0}`, the limit taken within
`ℝ^{n+2}_{≥0}` (equivalently, as the book notes, for every `S` and `δ > 0` there is an `ε > 0`
with `f(S) − δ < f(S')` for all `S' ∈ ℝ^{n+2}_{≥0} ∩ N_ε(S)`). -/
def IsLowerSemicontinuous (f : (Fin (n + 2) → ℝ) → ℝ) : Prop :=
  LowerSemicontinuousOn f (orthant n)

/-- Definition 3.3.7 (p. 230): `f` is locally regular (class 6) if `f` is lower semicontinuous
on `ℝ^{n+2}_{≥0}` and regular on the equal-order set `S_T^=(O(S))` for each `S ∈ 𝒮`. -/
def IsLocallyRegular (P : Project n K) (f : (Fin (n + 2) → ℝ) → ℝ) : Prop :=
  IsLowerSemicontinuous f ∧ ∀ S ∈ feasibleSet P, IsRegularOn (equalOrderSet P S) f

/-- Definition 3.3.11 (p. 233): `f` is locally quasiconcave (class 7) if `f` is lower
semicontinuous on `ℝ^{n+2}_{≥0}` and quasiconcave on the equal-order set `S_T^=(O(S))` for each
`S ∈ 𝒮`. -/
def IsLocallyQuasiconcave (P : Project n K) (f : (Fin (n + 2) → ℝ) → ℝ) : Prop :=
  IsLowerSemicontinuous f ∧ ∀ S ∈ feasibleSet P, IsQuasiconcaveOn (equalOrderSet P S) f

/-- §3.1 (p. 203): the peak `max_t r_k(S, t)` of the resource profile of resource `k`, the
maximum taken over all `t ≥ 0`. The set of values is nonempty (`t = 0`) and finite (at most one
value per subset of `V`), so the supremum in `ℕ` is attained. For feasible `S` every activity
ends by `S_{n+1} ≤ d̄`, and this is the book's `max_{0 ≤ t ≤ d̄} r_k(S, t)`. -/
noncomputable def peakUsage (P : Project n K) (S : Fin (n + 2) → ℝ) (k : K) : ℕ :=
  sSup {u | ∃ t : ℝ, 0 ≤ t ∧ usage P S k t = u}

/-- §3.1 (p. 203): the resource investment objective
`∑ c_k max r_kt = ∑_{k ∈ 𝓡} c_k max_t r_k(S, t)`, with procurement costs `c_k` per unit of
resource `k`. -/
noncomputable def resourceInvestment [Fintype K] (P : Project n K) (c : K → ℝ)
    (S : Fin (n + 2) → ℝ) : ℝ :=
  ∑ k, c k * (peakUsage P S k : ℝ)

end ProjSchedTW.ObjectiveClasses



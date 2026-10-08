-- Prove2me | Definitions.Def_ProjSchedTW_StableSchedules_Shifts
-- name    : ProjSchedTW_StableSchedules_Shifts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T00:53:38.510678+00:00
-- url     : https://prove2.me/theorems/e66dc404-56e3-4b41-983b-fa616862e77b
-- title:
--   Definitions 2.4.1–2.4.6, 3.2.1, 3.2.2, 3.2.5, 3.2.6 — shifts, active and stable schedule classes, local extreme points
-- statement:
--   This file defines the kinds of shifts between schedules and the schedule classes of §2.4 and §3.2.
--
--   **Shifts.** A shift transforms a schedule $S$ into a schedule $S'\neq S$. It is a **left-shift** if $S'\le S$ and a **right-shift** if $S'\ge S$ (componentwise). For feasible $S, S'\in\mathcal S$, a shift from $S$ to $S'$ is
--
--   1. **global** in every case (Definition 2.4.2);
--   2. **local** if there is a continuous trajectory $x:[0,1]\to\mathcal S$ with $x(0)=S$ and $x(1)=S'$ (Definition 2.4.3);
--   3. **order-preserving** if $O(S)\subseteq O(S')$, and **order-monotone** if $O(S)\subseteq O(S')$ or $O(S)\supseteq O(S')$ (Definition 2.4.4).
--
--   A shift is **uniform** if $S'-S=\lambda z$ with $z\in\{0,1\}^{n+2}$ and $\lambda\ne 0$ (Definition 3.2.1). Two shifts from $S$ to $S'$ and to $S''$ are **opposite** if
--   $$S''-S=\lambda\,(S'-S)\quad\text{for some }\lambda<0$$
--   (Definition 3.2.2).
--
--   **Schedule classes.** A feasible schedule is *active*, *semiactive*, *pseudoactive* or *quasiactive* if there is no global, local, order-monotone or order-preserving left-shift from it, respectively (Definition 2.4.6). It is *antiactive* if there is no global right-shift from it (Definition 3.2.5). It is *stable*, *semistable*, *pseudostable* or *quasistable* if there is no pair of opposite global, local, order-monotone or order-preserving shifts from it, respectively (Definition 3.2.6).
--
--   **Local extreme point** (p. 210). A point $S\in M$ is a local extreme point of $M\subseteq\mathbb R^{n+2}$ if it does not lie on a line segment that joins two other points of $M$ and lies entirely in $M$.
--
--   The theorems of §3.2 identify these shift-defined classes with geometric points of the feasible region.
--
--   **Formalization Note** The left-shift predicate $S'\le S,\ S'\neq S$ is not restated here: it is `ProjSchedTW.ActiveSchedules.IsLeftShift`, imported from the definitions of §2.4 (Definitions 2.4.1–2.4.6), and the four left-shift classes use it. "Pair of opposite shifts of type X from $S$" means that both shifts, $S\to S'$ and $S\to S''$, are of type X. A local extreme point of $M$ is written as follows: whenever the closed segment $[x_1,x_2]$ lies in $M$ and $S$ lies in the open segment, then $x_1=x_2=S$.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 39 (Definitions 2.4.1–2.4.4), pp. 41–42 (Definition 2.4.6), p. 207 (Definitions 3.2.1, 3.2.2), pp. 209–210 (Definitions 3.2.5, 3.2.6, local extreme point)

import Mathlib
import Definitions.Def_ProjSchedTW_StableSchedules_Project
import Definitions.Def_ProjSchedTW_ActiveSchedules_Shifts

namespace ProjSchedTW.StableSchedules

variable {n : ℕ} {K : Type}

/-- Definition 2.4.1 (p. 39): a right-shift from `S` to `S'`, in the book's brief form
`S' ≥ S` and `S' ≠ S`. -/
def IsRightShift (S S' : Fin (n + 2) → ℝ) : Prop :=
  S ≤ S' ∧ S' ≠ S

/-- Definition 2.4.2 (p. 39): a global shift transforms a feasible schedule `S` into a feasible
schedule `S' ≠ S`. -/
def IsGlobalShift (P : Project n K) (S S' : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧ S' ∈ feasibleSet P ∧ S' ≠ S

/-- Definition 2.4.3 (p. 39): a local shift is a global shift from `S` to `S'` for which there
is a continuous trajectory `x : [0, 1] → 𝒮` with `x(0) = S` and `x(1) = S'`. -/
def IsLocalShift (P : Project n K) (S S' : Fin (n + 2) → ℝ) : Prop :=
  IsGlobalShift P S S' ∧
    ∃ x : unitInterval → (Fin (n + 2) → ℝ), Continuous x ∧ x 0 = S ∧ x 1 = S' ∧
      ∀ τ, x τ ∈ feasibleSet P

/-- Definition 2.4.4 (p. 39): a shift between feasible schedules is order-preserving if
`O(S) ⊆ O(S')`. -/
def IsOrderPreservingShift (P : Project n K) (S S' : Fin (n + 2) → ℝ) : Prop :=
  IsGlobalShift P S S' ∧ scheduleOrder P S ⊆ scheduleOrder P S'

/-- Definition 2.4.4 (p. 39): a shift between feasible schedules is order-monotone if
`O(S) ⊆ O(S')` or `O(S) ⊇ O(S')`. -/
def IsOrderMonotoneShift (P : Project n K) (S S' : Fin (n + 2) → ℝ) : Prop :=
  IsGlobalShift P S S' ∧
    (scheduleOrder P S ⊆ scheduleOrder P S' ∨ scheduleOrder P S' ⊆ scheduleOrder P S)

/-- Definition 3.2.1 (p. 207): a shift from `S` to `S' ≠ S` is uniform if `S' − S = λ z` with
`z ∈ {0, 1}^{n+2}` and `λ ≠ 0`. -/
def IsUniformShift (S S' : Fin (n + 2) → ℝ) : Prop :=
  S' ≠ S ∧ ∃ z : Fin (n + 2) → ℝ, (∀ i, z i = 0 ∨ z i = 1) ∧
    ∃ lam : ℝ, lam ≠ 0 ∧ S' - S = lam • z

/-- Definition 3.2.2 (p. 207): two shifts from `S` to `S'` and to `S''` (so `S' ≠ S` and
`S'' ≠ S`) are opposite if `S'' − S = λ (S' − S)` for some `λ < 0`. -/
def AreOpposite (S S' S'' : Fin (n + 2) → ℝ) : Prop :=
  S' ≠ S ∧ S'' ≠ S ∧ ∃ lam : ℝ, lam < 0 ∧ S'' - S = lam • (S' - S)

/-- Definition 2.4.6 (pp. 41–42): a feasible schedule is active if there is no global
left-shift from it (the set `AS`). -/
def IsActive (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧ ¬ ∃ S', IsGlobalShift P S S' ∧ ProjSchedTW.ActiveSchedules.IsLeftShift S S'

/-- Definition 2.4.6 (pp. 41–42): a feasible schedule is semiactive if there is no local
left-shift from it (the set `SAS`). -/
def IsSemiactive (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧ ¬ ∃ S', IsLocalShift P S S' ∧ ProjSchedTW.ActiveSchedules.IsLeftShift S S'

/-- Definition 2.4.6 (pp. 41–42): a feasible schedule is pseudoactive if there is no
order-monotone left-shift from it (the set `PAS`). -/
def IsPseudoactive (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧ ¬ ∃ S', IsOrderMonotoneShift P S S' ∧ ProjSchedTW.ActiveSchedules.IsLeftShift S S'

/-- Definition 2.4.6 (pp. 41–42): a feasible schedule is quasiactive if there is no
order-preserving left-shift from it (the set `QAS`). -/
def IsQuasiactive (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧ ¬ ∃ S', IsOrderPreservingShift P S S' ∧ ProjSchedTW.ActiveSchedules.IsLeftShift S S'

/-- Definition 3.2.5 (p. 209): a feasible schedule is antiactive if there is no global
right-shift from it (the set `\overline{AS}`). -/
def IsAntiactive (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧ ¬ ∃ S', IsGlobalShift P S S' ∧ IsRightShift S S'

/-- Definition 3.2.6 (p. 210): a feasible schedule is stable if there is no pair of opposite
global shifts from it (the set `SS`). -/
def IsStable (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧
    ¬ ∃ S' S'', IsGlobalShift P S S' ∧ IsGlobalShift P S S'' ∧ AreOpposite S S' S''

/-- Definition 3.2.6 (p. 210): a feasible schedule is semistable if there is no pair of opposite
local shifts from it (the set `SSS`). -/
def IsSemistable (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧
    ¬ ∃ S' S'', IsLocalShift P S S' ∧ IsLocalShift P S S'' ∧ AreOpposite S S' S''

/-- Definition 3.2.6 (p. 210): a feasible schedule is pseudostable if there is no pair of
opposite order-monotone shifts from it (the set `PSS`). -/
def IsPseudostable (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧
    ¬ ∃ S' S'', IsOrderMonotoneShift P S S' ∧ IsOrderMonotoneShift P S S'' ∧
      AreOpposite S S' S''

/-- Definition 3.2.6 (p. 210): a feasible schedule is quasistable if there is no pair of
opposite order-preserving shifts from it (the set `QSS`). -/
def IsQuasistable (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧
    ¬ ∃ S' S'', IsOrderPreservingShift P S S' ∧ IsOrderPreservingShift P S S'' ∧
      AreOpposite S S' S''

/-- §3.2, p. 210: `S ∈ M` is a local extreme point of `M` if `S` does not lie on a line segment
that joins two other points of `M` and totally belongs to `M`: whenever the closed segment
`[x₁, x₂]` is contained in `M` and `S` lies in its relative interior, `x₁ = x₂ = S`. -/
def IsLocalExtremePoint (M : Set (Fin (n + 2) → ℝ)) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ M ∧ ∀ x₁ x₂ : Fin (n + 2) → ℝ, segment ℝ x₁ x₂ ⊆ M → S ∈ openSegment ℝ x₁ x₂ →
    x₁ = S ∧ x₂ = S

end ProjSchedTW.StableSchedules



-- Prove2me | Definitions.Def_TightReleaseSchedules_Stationary_Supplement_schedules
-- name    : TightReleaseSchedules_Stationary_Supplement_schedules
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:17:29.962062+00:00
-- url     : https://prove2.me/theorems/6fcdccfb-7564-4b97-83c9-3d1f71db186b
-- title:
--   Integer release schedules and their phase lengths
-- statement:
--   Fix a horizon $T$ and a release budget $B\ge0$. An **integer release schedule** is a vector of $B+2$ natural numbers
--
--   $$
--   0=\tau_0\le\tau_1\le\cdots\le\tau_B\le\tau_{B+1}=T .
--   $$
--
--   Equal dates are allowed, so a schedule may use fewer than $B$ releases, and unused releases are padded at $T$. Phase $j\in\{0,\dots,B\}$ consists of rounds $\tau_j+1,\dots,\tau_{j+1}$ and has length $L_j=\tau_{j+1}-\tau_j$. Release slot $j\in\{1,\dots,B\}$ of a policy carries the date $\tau_j$.
--
--   The set of schedules is finite and nonempty (it contains $(0,T,\dots,T)$), so for any real-valued program $F$ on schedules the infimum of $F$ over schedules is a minimum. These notions are shared by the release-design programs $E(\tau)$ of Theorem 4.3 and $F(\tau)$ of Theorem 5.1.
--
--   **Formalization Note** A schedule is a function `Fin (B + 2) → ℕ`; the minimum is the real `sInf` of the finite nonempty image, which is attained.
-- source:
--   Jing Wang, When to Update a Pretrained Model: Tight Release Schedules under Distribution Shift, STOC 2027 submission #1096 (October 2026), §3.1, printed p.6, PDF p.7; Theorem 4.3, printed p.13, PDF p.14; §5, printed p.15, PDF p.16

import Definitions.Def_TightReleaseSchedules_Stationary_geometric_algorithm

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace TightReleaseSchedules.Stationary.Supplement

open TightReleaseSchedules.Stationary

/-- An integer release schedule `0 = τ₀ ≤ τ₁ ≤ ⋯ ≤ τ_B ≤ τ_{B+1} = T`, stored as `B + 2`
natural numbers. Equal dates (zero-length phases) and padding by `T` are allowed. -/
def IsSchedule (T B : ℕ) (τ : Fin (B + 2) → ℕ) : Prop :=
  τ 0 = 0 ∧ τ (Fin.last (B + 1)) = T ∧ Monotone τ

/-- The date `τ_j` that opens phase `j`, for `j = 0, …, B`. -/
def phaseStart {B : ℕ} (τ : Fin (B + 2) → ℕ) (j : Fin (B + 1)) : ℕ := τ j.castSucc

/-- The phase length `L_j = τ_{j+1} − τ_j`, as a real number. -/
def phaseLength {B : ℕ} (τ : Fin (B + 2) → ℕ) (j : Fin (B + 1)) : ℝ :=
  (τ j.succ : ℝ) - (τ j.castSucc : ℝ)

/-- Release slot `j` of a `B`-slot policy carries the schedule date `τ_{j+1}`. -/
def slotDate {B : ℕ} (τ : Fin (B + 2) → ℕ) (j : Fin B) : ℕ := τ j.succ.castSucc

/-- The finite set of schedules is nonempty (`τ = (0, T, …, T)`), so this real infimum of
the program values is their minimum. -/
def scheduleMin (T B : ℕ) (F : (Fin (B + 2) → ℕ) → ℝ) : ℝ :=
  sInf (F '' {τ | IsSchedule T B τ})

end TightReleaseSchedules.Stationary.Supplement



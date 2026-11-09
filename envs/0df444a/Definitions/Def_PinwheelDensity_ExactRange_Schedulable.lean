-- Prove2me | Definitions.Def_PinwheelDensity_ExactRange_Schedulable
-- name    : PinwheelDensity_ExactRange_Schedulable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:16.002219+00:00
-- url     : https://prove2.me/theorems/894a8c03-aeae-42c8-a7b3-b422a6c1e86d
-- title:
--   Pinwheel instances, schedules over ℕ and ℤ, density, saturation and the threshold $G(m)$
-- statement:
--   A **pinwheel instance** is a finite list $A=(a_1,\dots,a_k)$ of positive integer periods; equal values at different positions are different tasks. Its **density** is $D(A)=\sum_i 1/a_i$, computed exactly in $\mathbb Q$.
--
--   A one-sided **schedule** assigns to each day $d\in\mathbb N$ at most one task, and $A$ is **schedulable** when every task $i$ executes in every window $[t,t+a_i)$. No periodicity is required, and the empty list is schedulable. A **periodic idle-free schedule** in addition has no idle day and repeats with some period $P\ge 1$.
--
--   A **schedule over $\mathbb Z$** (Section 2) is a family of pairwise disjoint sets $S_i\subseteq\mathbb Z$ with $S_i\cap[t,t+a_i)\ne\emptyset$ for all $i$ and all $t\in\mathbb Z$. A **free day** lies in no $S_i$, and $A$ is **saturated** when it has a schedule over $\mathbb Z$ and no schedule over $\mathbb Z$ has a free day.
--
--   For Appendix A's **rational periods**, a schedule is a map $s:\mathbb N\to\mathbb N\cup\{\bot\}$, $\mathrm{cnt}_i(t,w)=\#\{k<w:s(t+k)=i\}$, and task $i$ is **served with period** $a>0$ when $\mathrm{cnt}_i(t,w)\ge\lfloor w/a\rfloor$ for all $t,w\in\mathbb N$. A list of positive rationals is schedulable when one schedule serves every position.
--
--   Finally,
--   $$c(m)=1-\frac{m-1}{m(m+1)},$$
--   **Conjecture 1.1 at $m$** says that every list of positive integers with smallest period exactly $m$ and density at most $c(m)$ is schedulable, and $G(m)$ is the real supremum of the set $T(m)$ of $\delta$ such that every list of positive integers with all periods at least $m$ and density at most $\delta$ is schedulable.
--
--   These objects carry every statement of the mission.
--
--   **Formalization Note** The positivity of periods is stated explicitly wherever a list is quantified over, because $1/0=0$ in `ℚ`. Positivity is part of `RatSchedulable`, because $\lfloor w/a\rfloor$ would impose nothing for $a\le 0$. `G` is applied only for $m\ge1$, where $T(m)$ contains $0$ and is bounded above.
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Section 1, pp. 1–2; Section 2, pp. 3–4; Appendix A, p. 9; Appendix B, p. 11 (same PDF pages)

import Mathlib

namespace PinwheelDensity.ExactRange

/-- Density `D(A) = ∑ᵢ 1/aᵢ` of a list of integer periods, computed in `ℚ`. A period `0` would
contribute `1/0 = 0` here; every use below requires all periods to be positive. -/
def density (A : List ℕ) : ℚ :=
  (A.map fun a => (1 : ℚ) / (a : ℚ)).sum

/-- Density of a list of rational periods (Appendix A, p. 9). -/
def densityQ (A : List ℚ) : ℚ :=
  (A.map fun a => (1 : ℚ) / a).sum

/-- Classical one-sided pinwheel schedulability (Section 1, p. 1; Lemma A.1, p. 9): a schedule
assigns to every day `d : ℕ` at most one position of the list (`none` is an idle day), and task `i`
executes in every window `[t, t + aᵢ)`. Equal periods at different positions are different tasks.
There is no periodicity requirement. A zero period makes the window empty, hence unschedulable. -/
def Schedulable (A : List ℕ) : Prop :=
  ∃ s : ℕ → Option (Fin A.length),
    ∀ (i : Fin A.length) (t : ℕ), ∃ d : ℕ, t ≤ d ∧ d < t + A.get i ∧ s d = some i

/-- A periodic idle-free schedule (Lemma A.1, p. 9): every day runs a task, the day assignment has
some period `P ≥ 1`, and task `i` executes in every window `[t, t + aᵢ)`. -/
def HasPeriodicIdleFreeSchedule (A : List ℕ) : Prop :=
  ∃ (P : ℕ) (s : ℕ → Fin A.length), 0 < P ∧ (∀ t, s (t + P) = s t) ∧
    ∀ (i : Fin A.length) (t : ℕ), ∃ d : ℕ, t ≤ d ∧ d < t + A.get i ∧ s d = i

/-- A schedule over `ℤ` in the sense of Section 2, p. 3: pairwise disjoint day sets `Sᵢ ⊆ ℤ` with
`Sᵢ ∩ [t, t + aᵢ) ≠ ∅` for every task `i` and every integer `t`. -/
structure ZSchedule (A : List ℕ) where
  /-- The execution days of each task. -/
  days : Fin A.length → Set ℤ
  /-- At most one task runs per day. -/
  disjoint : Pairwise fun i j => Disjoint (days i) (days j)
  /-- Every window of `aᵢ` consecutive integers contains an execution of task `i`. -/
  hits : ∀ (i : Fin A.length) (t : ℤ),
    (days i ∩ Set.Ico t (t + (A.get i : ℤ))).Nonempty

/-- Existence of a schedule over `ℤ`. -/
def ZSchedulable (A : List ℕ) : Prop :=
  Nonempty (ZSchedule A)

/-- A free day of a schedule over `ℤ` (pp. 3–4): an integer in no `Sᵢ`. -/
def ZSchedule.IsFreeDay {A : List ℕ} (σ : ZSchedule A) (d : ℤ) : Prop :=
  ∀ i : Fin A.length, d ∉ σ.days i

/-- No schedule of `A` over `ℤ` has a free day. -/
def NoScheduleWithFreeDay (A : List ℕ) : Prop :=
  ∀ (σ : ZSchedule A) (d : ℤ), ¬ σ.IsFreeDay d

/-- Saturation (p. 4): schedulable over `ℤ`, and no schedule over `ℤ` has a free day. This is a
two-sided notion: one-sided schedules of saturated instances can have free days (Remark 2.5). -/
def Saturated (A : List ℕ) : Prop :=
  ZSchedulable A ∧ NoScheduleWithFreeDay A

/-- `cntᵢ(t, w) = #{k < w : s(t + k) = i}` for a schedule `s : ℕ → ℕ ∪ {⊥}` (Appendix A, p. 9). -/
def cnt (s : ℕ → Option ℕ) (i t w : ℕ) : ℕ :=
  ((List.range w).filter fun k => s (t + k) = some i).length

/-- Task `i` is served with rational period `a`: `cntᵢ(t, w) ≥ ⌊w / a⌋` for all `t, w ∈ ℕ`
(Appendix A, p. 9). This is meaningful for `a > 0`, which `RatSchedulable` requires. -/
def Serves (s : ℕ → Option ℕ) (i : ℕ) (a : ℚ) : Prop :=
  ∀ t w : ℕ, ⌊(w : ℚ) / a⌋₊ ≤ cnt s i t w

/-- Schedulability of a list of positive rationals (Appendix A, p. 9): the entries are positive and
one schedule serves every position `i` with period `Aᵢ`. A symbol that is not a position of the list
behaves as an idle day. -/
def RatSchedulable (A : List ℚ) : Prop :=
  (∀ a ∈ A, 0 < a) ∧
    ∃ s : ℕ → Option ℕ, ∀ (i : ℕ) (hi : i < A.length), Serves s i A[i]

/-- An integer list viewed as a list of rational periods. -/
def toQ (A : List ℕ) : List ℚ :=
  A.map fun a => (a : ℚ)

/-- `m` is the smallest period of `A`; in particular `A` is nonempty. -/
def IsMinPeriod (m : ℕ) (A : List ℕ) : Prop :=
  m ∈ A ∧ ∀ a ∈ A, m ≤ a

/-- Kawamura's bound `c(m) = 1 - (m - 1)/(m (m + 1))` (p. 2), computed in `ℚ`. -/
def c (m : ℕ) : ℚ :=
  1 - ((m : ℚ) - 1) / ((m : ℚ) * ((m : ℚ) + 1))

/-- Conjecture 1.1 (p. 2) for the value `m` of the smallest period: every nonempty list of positive
integer periods with smallest period exactly `m` and density at most `c(m)` is schedulable. -/
def ConjectureAt (m : ℕ) : Prop :=
  ∀ A : List ℕ, (∀ a ∈ A, 1 ≤ a) → IsMinPeriod m A → density A ≤ c m → Schedulable A

/-- `S(m, B)` (Appendix B, p. 11): every finite list of positive integers with all periods at least
`m` and density at most `B` is schedulable. The empty list is included. -/
def Guarantee (m : ℕ) (B : ℚ) : Prop :=
  ∀ A : List ℕ, (∀ a ∈ A, 1 ≤ a ∧ m ≤ a) → density A ≤ B → Schedulable A

/-- The threshold set: real `δ` such that every list of positive integers with all periods at least
`m` and density at most `δ` is schedulable. -/
def ThresholdSet (m : ℕ) : Set ℝ :=
  {δ | ∀ A : List ℕ, (∀ a ∈ A, 1 ≤ a ∧ m ≤ a) → ((density A : ℚ) : ℝ) ≤ δ → Schedulable A}

/-- `G(m)` (p. 2): the supremum of the threshold set, a real supremum. The set contains `0` and,
for `m ≥ 1`, is bounded above (Proposition 2.3). -/
noncomputable def G (m : ℕ) : ℝ :=
  sSup (ThresholdSet m)

end PinwheelDensity.ExactRange



-- Prove2me | Definitions.Def_SchoolChoice_TTC_Algorithm
-- name    : SchoolChoice_TTC_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T07:18:59.782046+00:00
-- url     : https://prove2.me/theorems/6bab3da4-bc50-4633-876b-5785d4d951c1
-- title:
--   The top trading cycles algorithm for school choice
-- statement:
--   This file defines the **top trading cycles (TTC) algorithm** of Abdulkadiroğlu and Sönmez as a concrete, deterministic procedure, run on capacities $q=(q_s)_{s\in S}$, priorities $(\succ_s)_{s\in S}$ and an announced preference profile $P=(P_i)_{i\in I}$.
--
--   A **state** of the algorithm records the set $R\subseteq I$ of remaining students, a **counter** $c_s\in\mathbb N$ for each school (seats still available) and the school assigned so far to each removed student. Initially $R=I$, $c_s=q_s$ and nobody is assigned. The **remaining schools** are those with $c_s>0$; a school whose counter has reached zero (or whose capacity is zero) is removed.
--
--   At each step:
--
--   1. every remaining student points to her favourite remaining school under her announced preference;
--   2. every remaining school points to the remaining student with the highest priority for it;
--   3. a **cycle** is an ordered list $(s_1,i_1,s_2,\dots,s_k,i_k)$ of distinct schools and distinct students in which $s_1$ points to $i_1$, $i_1$ points to $s_2$, …, $s_k$ points to $i_k$ and $i_k$ points to $s_1$;
--   4. **every** student lying on **some** cycle is assigned a seat at the school she points to and is removed, and the counter of each school on a cycle is reduced by one; counters of all other schools stay put.
--
--   All cycles present at a step are cleared at that same step. Writing $\mathrm{run}(t)$ for the state after $t$ completed steps, $\mathrm{run}(0)$ is the beginning of the paper's Step 1 and $\mathrm{run}(t)$ is the beginning of Step $t+1$. The **top trading cycles mechanism** returns the assignment recorded after $|I|$ steps:
--   $$\mathrm{TTC}(q,\succ,P)(i) = \text{the school assigned to } i \text{ in } \mathrm{run}(|I|).$$
--
--   This definition is the object of every theorem of the mission: termination, Pareto efficiency (Proposition 3) and strategy-proofness (Proposition 4).
--
--   **Formalization Note** A student is on a cycle iff following the pointers student → school → student from her returns to her within at most $|I|$ rounds; because every school points to a single student, the schools of such a cycle are automatically distinct. The mechanism is total: it always runs exactly $|I|$ steps and returns an `Option S` per student, where `none` would mean "not assigned". That every value is `some` under the paper's no-shortage assumption is a theorem of the mission, not part of the definition. A step with no cycle leaves the state unchanged.
-- source:
--   Abdulkadiroğlu and Sönmez, School Choice: A Mechanism Design Approach, Columbia Univ. Economics Discussion Paper No. 0203-18 (July 2003), pp. 15–16, Section II.B (the top trading cycles algorithm, Step 1 and Step k)

import Mathlib
import Definitions.Def_SchoolChoice_TTC_Model

namespace SchoolChoice.TTC

variable {I S : Type} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]

/-- The best element of a finite set `T` under a ranking `r` (the element of least rank),
or `none` if `T` is empty. -/
def bestIn {α : Type} {n : ℕ} (r : α ≃ Fin n) (T : Finset α) : Option α :=
  if h : T.Nonempty then some (r.symm ((T.image r).min' (h.image r))) else none

/-- The state of the top trading cycles algorithm between two steps:
`rem` is the set of remaining students, `cnt s` the counter of school `s`
(seats still available), and `asg i` the school assigned so far to student `i`
(`none` while `i` has not been assigned). -/
structure State (I S : Type) where
  rem : Finset I
  cnt : S → ℕ
  asg : I → Option S

/-- The initial state (beginning of Step 1): every student remains, the counters equal
the capacities, and nobody is assigned. -/
def init (q : S → ℕ) : State I S :=
  ⟨Finset.univ, q, fun _ => none⟩

/-- The remaining schools: those whose counter is positive. A school whose counter has
reduced to zero is removed; a school of capacity `0` is never remaining. -/
def remSchools (st : State I S) : Finset S :=
  Finset.univ.filter (fun s => 0 < st.cnt s)

/-- The school a student `i` points to: her favourite school among the remaining schools
under her announced preference `P i` (`none` if no school remains). -/
def pointS (P : I → Pref S) (st : State I S) (i : I) : Option S :=
  bestIn (P i) (remSchools st)

/-- The student a school `s` points to: the remaining student with the highest priority
for `s` (`none` if no student remains). -/
def pointI (pri : S → Priority I) (st : State I S) (s : S) : Option I :=
  bestIn (pri s) st.rem

/-- One round of pointing, from students to students: `i` points to the school
`pointS P st i`, which points to the student `pointI pri st (pointS P st i)`. -/
def nextO (P : I → Pref S) (pri : S → Priority I) (st : State I S) (o : Option I) :
    Option I :=
  (o.bind (pointS P st)).bind (pointI pri st)

/-- A remaining student `i` is in a cycle `(s₁, i₁, s₂, …, s_k, i_k)` of the current
pointing graph iff following the pointers from `i` (student → school → student) returns
to `i`. Every periodic point of a map on `I` has a period at most `card I`, so it suffices
to look at `n + 1` rounds with `n < card I`. -/
def InCycle (P : I → Pref S) (pri : S → Priority I) (st : State I S) (i : I) : Prop :=
  i ∈ st.rem ∧ ∃ n ∈ Finset.range (Fintype.card I),
    (nextO P pri st)^[n + 1] (some i) = some i

instance (P : I → Pref S) (pri : S → Priority I) (st : State I S) :
    DecidablePred (InCycle P pri st) := fun i => by
  unfold InCycle; infer_instance

/-- The set of students who are in a cycle at the current state. -/
def cycleStudents (P : I → Pref S) (pri : S → Priority I) (st : State I S) : Finset I :=
  st.rem.filter (InCycle P pri st)

/-- One step of the top trading cycles algorithm (Section II.B, pp. 15–16). **All cycles
present at the step are executed simultaneously**: every student in a cycle is assigned
a seat at the school she points to and is removed, and the counter of each school is
reduced by the number of cycle students pointing to it (which is one for a school in a
cycle and zero otherwise; counters of all other schools stay put). A school whose
counter reaches zero is thereby removed (see `remSchools`). -/
def step (P : I → Pref S) (pri : S → Priority I) (st : State I S) : State I S :=
  let C := cycleStudents P pri st
  { rem := st.rem \ C
    cnt := fun s => st.cnt s - (C.filter (fun i => pointS P st i = some s)).card
    asg := fun i => if i ∈ C then pointS P st i else st.asg i }

/-- `run q pri P t` is the state after `t` completed steps of the algorithm, i.e. the
state at the **beginning of Step `t + 1`** in the paper's numbering (`run … 0` is the
beginning of Step 1). -/
def run (q : S → ℕ) (pri : S → Priority I) (P : I → Pref S) (t : ℕ) : State I S :=
  (step P pri)^[t] (init q)

/-- The top trading cycles mechanism (Section II.B, pp. 15–16): the assignment produced
after `card I` steps of the algorithm, run on capacities `q`, priorities `pri` and the
announced preference profile `P`. The paper notes that there can be no more steps than
the number of students; the value `none` would mean that a student is left unassigned. -/
def ttc (q : S → ℕ) (pri : S → Priority I) (P : I → Pref S) : I → Option S :=
  (run q pri P (Fintype.card I)).asg

end SchoolChoice.TTC



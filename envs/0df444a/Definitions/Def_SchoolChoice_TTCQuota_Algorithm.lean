-- Prove2me | Definitions.Def_SchoolChoice_TTCQuota_Algorithm
-- name    : SchoolChoice_TTCQuota_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T07:56:09.568929+00:00
-- url     : https://prove2.me/theorems/3769272d-13d4-45d7-8683-bca8d214d424
-- title:
--   The top trading cycles algorithm with type-specific quotas
-- statement:
--   This file defines the **top trading cycles mechanism with type-specific quotas** of Abdulkadiroğlu and Sönmez (Section III.B), as a deterministic algorithm.
--
--   The input consists of capacities $q_s$, type quotas $q_s^t$, student types $\tau(i)$, school priorities, and the students' announced strict preferences $P=(P_i)_{i\in I}$. The algorithm keeps a set of remaining students, a counter $c_s$ for each school (initially $q_s$) and a type-specific counter $c_s^t$ for each school and type (initially $q_s^t$). A school is **remaining** while $c_s>0$; it **has room for type $t$** when $c_s>0$ and $c_s^t>0$. A school is removed when its total counter reaches zero, not when a type-specific counter does.
--
--   Each step $k=1,2,\dots$ does the following.
--
--   1. Every remaining student who has no remaining school with room for her type is removed without an assignment (see the Formalization Note).
--   2. Every remaining student points to her favourite school, under her announced preference, among those with room for her type. Every remaining school points to the remaining student with the highest priority for it, whatever that student's type.
--   3. Every student in a cycle of this pointing graph (a list $s_1,i_1,\dots,s_k,i_k$ in which each school points to the next student and each student to the next school, cyclically) is assigned a seat at the school she points to and is removed. All cycles present at the step are cleared simultaneously.
--   4. The counter $c_s$ of each school in a cycle decreases by one, and so does its type-specific counter $c_s^{t}$ for the type $t$ of the student it is assigned to. All other counters stay put.
--
--   The outcome $\mathrm{TTC}^q(P)(i)$ is the school assigned to $i$ after $|I|$ steps, or $\varnothing$ if $i$ was removed without one. At most $|I|$ steps can do anything, since each step with a remaining student removes at least one.
--
--   This mechanism is the object of Propositions 6 (constrained efficiency) and 7 (strategy-proofness) of the paper. When every type quota is at least the capacity, it reduces to the plain top trading cycles mechanism of Section II.B.
--
--   **Formalization Note** The paper's step is undefined when a remaining student has no remaining school with room for her type: she cannot point, and a cycle need not exist. For example, one school with capacity $1$, quota $1$ for type $t_1$ and $0$ for type $t_2$, a student $a$ of type $t_2$ ranked first and a student $b$ of type $t_1$: $a$ cannot point, the school points to $a$, and there is no cycle although $b$ could be seated. The mission adopts the convention of item 1: such a *stuck* student is removed unassigned at the beginning of the step. Counters only decrease, so a stuck student would stay stuck. When no student is ever stuck, the algorithm is exactly the paper's. A step is indexed by the number $t$ of completed steps: $\mathrm{run}(t)$ is the state at the beginning of the paper's Step $t+1$, before that step's stuck removal. The outcome is total by construction, as an $|I|$-fold iteration of the step map.
-- source:
--   Abdulkadiroğlu and Sönmez, School Choice: A Mechanism Design Approach, Columbia Univ. Economics Discussion Paper No. 0203-18 (July 2003), p. 22, Section III.B (Step 1, Step k)

import Mathlib
import Definitions.Def_SchoolChoice_TTCQuota_Model

namespace SchoolChoice.TTCQuota

variable {I S Ty : Type} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
  [Fintype Ty] [DecidableEq Ty]

/-- The best element of a finite set `T` under a ranking `r` (the element of least rank),
or `none` if `T` is empty. -/
def bestIn {α : Type} {n : ℕ} (r : α ≃ Fin n) (T : Finset α) : Option α :=
  if h : T.Nonempty then some (r.symm ((T.image r).min' (h.image r))) else none

/-- The state of the top trading cycles algorithm with type-specific quotas between two
steps: `rem` is the set of remaining students, `cnt s` the (total) counter of school `s`
(seats still available), `tcnt s t` the type-specific counter of school `s` for type `t`,
and `asg i` the school assigned so far to student `i` (`none` while `i` has not been
assigned, and forever if `i` is removed unassigned). -/
structure State (I S Ty : Type) where
  rem : Finset I
  cnt : S → ℕ
  tcnt : S → Ty → ℕ
  asg : I → Option S

/-- The initial state (Step 1, Section III.B, p. 22): every student remains, each school's
counter equals its capacity `q s`, each type-specific counter equals the quota `qt s t` of
the associated type, and nobody is assigned. -/
def init (q : S → ℕ) (qt : S → Ty → ℕ) : State I S Ty :=
  ⟨Finset.univ, q, qt, fun _ => none⟩

/-- The remaining schools: those whose (total) counter is positive. A school is removed
when its total counter reduces to zero, not when a type-specific counter does; a school
of capacity `0` is never remaining. -/
def remSchools (st : State I S Ty) : Finset S :=
  Finset.univ.filter (fun s => 0 < st.cnt s)

/-- The remaining schools which have room for type `t`: positive total counter and
positive type-specific counter for `t`. -/
def roomFor (st : State I S Ty) (t : Ty) : Finset S :=
  Finset.univ.filter (fun s => 0 < st.cnt s ∧ 0 < st.tcnt s t)

/-- **Convention for the gap in the paper.** The paper's step is undefined when a remaining
student has no remaining school with room for her type (she cannot point). At the
beginning of every step, each such *stuck* remaining student is removed unassigned (her
assignment stays `none`). Since counters only decrease, a stuck student stays stuck.
`prune τ st` is the state after this removal. -/
def prune (τ : I → Ty) (st : State I S Ty) : State I S Ty :=
  { st with rem := st.rem.filter (fun i => (roomFor st (τ i)).Nonempty) }

/-- The school a student `i` points to: her favourite school, under her announced
preference `P i`, among the remaining schools which have room for her type `τ i`
(`none` if there is none). -/
def pointS (P : I → Pref S) (τ : I → Ty) (st : State I S Ty) (i : I) : Option S :=
  bestIn (P i) (roomFor st (τ i))

/-- The student a school `s` points to: the remaining student with the highest priority
for `s`, whatever her type (`none` if no student remains). -/
def pointI (pri : S → Priority I) (st : State I S Ty) (s : S) : Option I :=
  bestIn (pri s) st.rem

/-- One round of pointing, from students to students: `i` points to the school
`pointS P τ st i`, which points to the student `pointI pri st (pointS P τ st i)`. -/
def nextO (P : I → Pref S) (pri : S → Priority I) (τ : I → Ty) (st : State I S Ty)
    (o : Option I) : Option I :=
  (o.bind (pointS P τ st)).bind (pointI pri st)

/-- A remaining student `i` is in a cycle `(s₁, i₁, s₂, …, s_k, i_k)` of the pointing
graph of state `st` iff following the pointers from `i` (student → school → student)
returns to `i`. Every periodic point of a map on `I` has a period at most `card I`, so it
suffices to look at `n + 1` rounds with `n < card I`. -/
def InCycle (P : I → Pref S) (pri : S → Priority I) (τ : I → Ty) (st : State I S Ty)
    (i : I) : Prop :=
  i ∈ st.rem ∧ ∃ n ∈ Finset.range (Fintype.card I),
    (nextO P pri τ st)^[n + 1] (some i) = some i

instance (P : I → Pref S) (pri : S → Priority I) (τ : I → Ty) (st : State I S Ty) :
    DecidablePred (InCycle P pri τ st) := fun i => by
  unfold InCycle; infer_instance

/-- The set of students who are in a cycle at state `st`. -/
def cycleStudents (P : I → Pref S) (pri : S → Priority I) (τ : I → Ty)
    (st : State I S Ty) : Finset I :=
  st.rem.filter (InCycle P pri τ st)

/-- One step of the top trading cycles algorithm with type-specific quotas (Section III.B,
p. 22). First the stuck students are removed unassigned (`prune`, the convention above);
then, in the pruned state, every remaining student points to her favourite school with
room for her type and every remaining school points to its highest-priority remaining
student. **All cycles present are executed simultaneously**: every student in a cycle is
assigned a seat at the school she points to and is removed; the counter of each school
is reduced by the number of cycle students pointing to it (one for a school in a cycle,
zero otherwise), and its type-specific counter for type `t` by the number of those
students of type `t`. All other counters stay put. A school whose counter reaches zero
is thereby removed (see `remSchools`). -/
def step (P : I → Pref S) (pri : S → Priority I) (τ : I → Ty) (st : State I S Ty) :
    State I S Ty :=
  let st' := prune τ st
  let C := cycleStudents P pri τ st'
  { rem := st'.rem \ C
    cnt := fun s => st'.cnt s - (C.filter (fun i => pointS P τ st' i = some s)).card
    tcnt := fun s t =>
      st'.tcnt s t - (C.filter (fun i => pointS P τ st' i = some s ∧ τ i = t)).card
    asg := fun i => if i ∈ C then pointS P τ st' i else st'.asg i }

/-- `run q qt τ pri P t` is the state after `t` completed steps of the algorithm, i.e. the
state at the **beginning of Step `t + 1`** in the paper's numbering (`run … 0` is the
beginning of Step 1), before that step's removal of stuck students. -/
def run (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (pri : S → Priority I)
    (P : I → Pref S) (t : ℕ) : State I S Ty :=
  (step P pri τ)^[t] (init q qt)

/-- The top trading cycles mechanism with type-specific quotas (Section III.B, p. 22): the
assignment produced after `card I` steps of the algorithm, run on capacities `q`, type
quotas `qt`, student types `τ`, priorities `pri` and the announced preference profile `P`.
Every step with a remaining student removes at least one student, so `card I` steps
suffice. The value `none` means that the student was removed unassigned under the
stuck-student convention (see `prune`). -/
def ttcq (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (pri : S → Priority I)
    (P : I → Pref S) : I → Option S :=
  (run q qt τ pri P (Fintype.card I)).asg

end SchoolChoice.TTCQuota



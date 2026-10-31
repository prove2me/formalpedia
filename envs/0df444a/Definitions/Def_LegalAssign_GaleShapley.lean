-- Prove2me | Definitions.Def_LegalAssign_GaleShapley
-- name    : LegalAssign_GaleShapley
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:21:05.604716+00:00
-- url     : https://prove2.me/theorems/e5a71b2f-06da-45ad-a349-63f644a134ac
-- title:
--   The Gale–Shapley proposal process, student-proposing and school-proposing
-- statement:
--   The source cites Gale and Shapley and does not state the procedure. This definition is the standard proposal process. A **state** is a tentative assignment together with the set of pairs along which a proposal has been made, and the process starts with both empty.
--
--   **Student-proposing step.** A student $a$ holding no school, with a neighbour to whom $a$ has not yet proposed, proposes to the best such school $b$. The school keeps its $q_b$ best students among those it held and $a$, and rejects the others.
--
--   **School-proposing step.** A school $b$ holding fewer than $q_b$ students, with a neighbour to whom $b$ has not yet proposed, proposes to the best such student $a$. The student keeps the best school among the one held and $b$, and rejects the other.
--
--   An **output** is the tentative assignment of a state reachable from the initial state at which no step is possible. The choice of the proposer at each step is free, so a process has many executions.
--
--   **Formalization Note** `IsGSOutput step M` takes the step relation as a parameter; `G.StudentStep` and `G.SchoolStep` are the two relations.
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, Theorem 2.1, p.6 (the algorithm is cited from Gale and Shapley [15], not stated)

import Mathlib
import Definitions.Def_LegalAssign_Instance

namespace LegalAssign

/-- A state of the proposal process: the tentative assignment and the pairs already proposed. -/
structure GSState (A B : Type*) where
  /-- The tentative assignment. -/
  held : Finset (A × B)
  /-- The pairs along which a proposal has been made. -/
  proposed : Finset (A × B)

/-- The initial state: nothing held, nothing proposed. -/
def GSState.init (A B : Type*) : GSState A B := ⟨∅, ∅⟩

namespace Instance

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- `kept` is the set of the `q_b` best students of `pool` for school `b` (all of `pool` if it has at
most `q_b` students). -/
def IsKeptSet (G : Instance A B) (b : B) (pool kept : Finset A) : Prop :=
  kept ⊆ pool ∧ kept.card = min (G.q b) pool.card ∧
    ∀ a ∈ kept, ∀ a' ∈ pool, a' ∉ kept → G.prefB b a a'

/-- One step of student-proposing Gale–Shapley: a student `a` holding no school and with an
un-proposed neighbour proposes to the best such school `b`, which keeps its `q_b` best students among
those it held and `a`, and rejects the others.

**Formalization Note** arXiv:1809.08506v2 cites Gale and Shapley [15] and does not state the
procedure (Theorem 2.1, p.6). This is the standard proposal process; the proposer at each step is
arbitrary, so the theorem covers every execution. -/
def StudentStep (G : Instance A B) (s s' : GSState A B) : Prop :=
  ∃ (a : A) (b : B) (kept : Finset A),
    studentPartners s.held a = ∅ ∧ (a, b) ∈ G.E ∧ (a, b) ∉ s.proposed ∧
    (∀ b', (a, b') ∈ G.E → (a, b') ∉ s.proposed → b' ≠ b → G.prefA a b b') ∧
    G.IsKeptSet b (insert a (schoolPartners s.held b)) kept ∧
    s'.held = s.held.filter (fun e => e.2 ≠ b) ∪ kept.image (fun a' => (a', b)) ∧
    s'.proposed = insert (a, b) s.proposed

/-- One step of school-proposing Gale–Shapley: a school `b` holding fewer than `q_b` students and
with an un-proposed neighbour proposes to the best such student `a`, who keeps the best school `c`
among the one held and `b`, and rejects the other.

**Formalization Note** As for `StudentStep`, the procedure is the standard one and the proposer at
each step is arbitrary. -/
def SchoolStep (G : Instance A B) (s s' : GSState A B) : Prop :=
  ∃ (b : B) (a : A) (c : B),
    (schoolPartners s.held b).card < G.q b ∧ (a, b) ∈ G.E ∧ (a, b) ∉ s.proposed ∧
    (∀ a', (a', b) ∈ G.E → (a', b) ∉ s.proposed → a' ≠ a → G.prefB b a a') ∧
    c ∈ insert b (studentPartners s.held a) ∧
    (∀ c' ∈ insert b (studentPartners s.held a), c' ≠ c → G.prefA a c c') ∧
    s'.held = s.held.filter (fun e => e.1 ≠ a) ∪ {(a, c)} ∧
    s'.proposed = insert (a, b) s.proposed

/-- `M` is an output of the process with step relation `step`: the tentative assignment of a state
reachable from the initial state in which no step is possible. -/
def IsGSOutput (step : GSState A B → GSState A B → Prop) (M : Finset (A × B)) : Prop :=
  ∃ s, Relation.ReflTransGen step (GSState.init A B) s ∧ (¬ ∃ s', step s s') ∧ s.held = M

end Instance

end LegalAssign



-- Prove2me | Definitions.Def_Timetabling85_CourseColoring_CSUP
-- name    : Timetabling85_CourseColoring_CSUP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:45.429269+00:00
-- url     : https://prove2.me/theorems/67ebfce0-1642-4866-99cb-09c87e7f0d0c
-- title:
--   §3.1, p. 157 — course scheduling instances, feasible schedules, CSUP, the graph Ĝ of Prop. 3.1 and the graph Ĝ′ of Prop. 3.2
-- statement:
--   This file fixes the objects of §3.1 (*Basic formulation*) of de Werra's *An introduction to timetabling*.
--
--   1. **Course scheduling instance.** There are $q$ courses $K_b$, course $K_b$ consisting of $k_b$ lectures $l_a$, and $r$ students; student $i$ takes a set $T_i$ of courses (there is no fixed curriculum). A **lecture** is a pair $(b,a)$: lecture $l_a$ of course $K_b$; it is also the **lecture-node** $m_{ab}$ of the graph below.
--   2. **The lecture graph $G$.** Two distinct lecture-nodes are adjacent if they belong to the same course, or if they belong to two distinct courses $K_b \ne K_{\bar b}$ that some student takes together.
--   3. **Feasible schedule in $p$ periods.** A map $s$ from lectures to the periods $\{1,\dots,p\}$ such that
--      - two distinct lectures of the same course are at different periods, and
--      - whenever a student takes two distinct courses $K_b$ and $K_{\bar b}$, no lecture of $K_b$ is at the same period as a lecture of $K_{\bar b}$;
--
--      that is, no student is required to take more than one lecture at a time.
--   4. **CSUP.** A course scheduling problem with unavailabilities and preassignments in $p$ periods adds, for every course $K_b$, a set $U_b$ of periods at which $K_b$ cannot take place, and, for some lectures $l$, a period $\bar k(l)$ at which $l$ has to be scheduled. A **solution** is a feasible schedule $s$ with $s(l) \notin U_b$ for every lecture $l$ of $K_b$ and $s(l) = \bar k(l)$ for every preassigned lecture.
--   5. **The graph $\hat G$ (proof of Proposition 3.1).** Its nodes are the lecture-nodes and one **period-node** $k$ per period. Lecture-nodes are adjacent as in $G$; all pairs of period-nodes are adjacent; lecture-node $m_{ab}$ is adjacent to period-node $k$ if $k \in U_b$, or if $l_a$ is preassigned to a period $\bar k \ne k$.
--   6. **Removing precoloured nodes (Proposition 3.2).** Let $H$ be a graph on lecture-nodes $V$ and period-nodes $\{1,\dots,p\}$, and let some lecture-nodes $v$ be *precoloured* with the colour of a period-node $k(v)$. The graph $\hat G'$ has as nodes the lecture-nodes that are not precoloured and all period-nodes. Its edges are the edges of $H$ between these nodes, together with an edge $u\,k$ whenever $u$ is adjacent in $H$ to a precoloured node $v$ with $k(v) = k$: every precoloured node is removed and all its neighbours are linked with the period-node of its colour.
--
--   These are the objects of Propositions 3.1 and 3.2.
--
--   **Formalization Note** Courses, students, lectures of a course and periods are indexed from $0$ (`Fin q`, `Fin r`, `Fin (lectures b)`, `Fin p`). A lecture is a dependent pair `Σ b, Fin (lectures b)`. The nodes of $\hat G$ are `Lecture ⊕ Fin p` (`Sum.inl` for lecture-nodes, `Sum.inr` for period-nodes). Unavailability is per course and preassignment per lecture, as on the page; a lecture with no preassignment has `pre l = none`. The course clique (condition 1 of a feasible schedule) is part of feasibility even for a course no student takes, because the page's graph contains it. In $\hat G'$ a precoloured node is recorded as `pc v = some k`, "same colour as period-node $k$", which is how the proof of Proposition 3.1 removes a preassigned node.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), pp. 157–158, §3.1 (course scheduling problem and its graph, CSUP, the graph Ĝ in the proof of Proposition 3.1, the graph Ĝ′ of Proposition 3.2)

import Mathlib

namespace Timetabling85.CourseColoring

/-- A course scheduling instance (de Werra 1985, §3.1, p. 157): `q` courses `K_b` (`b : Fin q`),
course `K_b` consisting of `lectures b` lectures, and `r` students, student `i` taking the set of
courses `takes i`. There is no fixed curriculum: `takes` is arbitrary. -/
structure CourseInstance (q r : ℕ) where
  lectures : Fin q → ℕ
  takes : Fin r → Finset (Fin q)

namespace CourseInstance

variable {q r : ℕ}

/-- The lectures of an instance: `⟨b, a⟩` is lecture `l_a` of course `K_b` (the lecture-node
`m_ab` of the page). -/
abbrev Lecture (I : CourseInstance q r) : Type := Σ b : Fin q, Fin (I.lectures b)

/-- Two lectures are in conflict (adjacent in the graph of §3.1, p. 157) if they are distinct
lectures of the same course, or lectures of two distinct courses that some student takes
together. -/
def Conflict (I : CourseInstance q r) (l l' : I.Lecture) : Prop :=
  (l.1 = l'.1 ∧ l ≠ l') ∨ (l.1 ≠ l'.1 ∧ ∃ i : Fin r, l.1 ∈ I.takes i ∧ l'.1 ∈ I.takes i)

theorem conflict_symm (I : CourseInstance q r) {l l' : I.Lecture} (h : I.Conflict l l') :
    I.Conflict l' l := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, i, h3, h4⟩
  · exact Or.inl ⟨h1.symm, fun e => h2 e.symm⟩
  · exact Or.inr ⟨fun e => h1 e.symm, i, h4, h3⟩

theorem conflict_irrefl (I : CourseInstance q r) (l : I.Lecture) : ¬ I.Conflict l l := by
  rintro (⟨_, h⟩ | ⟨h, _⟩) <;> exact h rfl

/-- The graph of §3.1 (p. 157): one lecture-node per lecture, all pairs of lecture-nodes of a
course `K_b` joined, and every lecture-node of `K_b` joined to every lecture-node of `K_b̄`
whenever some student takes both `K_b` and `K_b̄` (`b ≠ b̄`). -/
def lectureGraph (I : CourseInstance q r) : SimpleGraph I.Lecture where
  Adj := I.Conflict
  symm := ⟨fun _ _ h => I.conflict_symm h⟩
  loopless := ⟨I.conflict_irrefl⟩

/-- A feasible course schedule in `p` periods (§3.1, p. 157): an assignment `s` of a period
`s l : Fin p` to every lecture such that
1. two distinct lectures of the same course take place at different periods, and
2. if a student takes two distinct courses `K_b` and `K_b̄`, no lecture of `K_b` takes place at
   the same period as a lecture of `K_b̄`
(no student is required to take more than one lecture at a time). -/
def IsFeasibleSchedule (I : CourseInstance q r) (p : ℕ) (s : I.Lecture → Fin p) : Prop :=
  (∀ (b : Fin q) (a a' : Fin (I.lectures b)), a ≠ a' → s ⟨b, a⟩ ≠ s ⟨b, a'⟩) ∧
  (∀ (i : Fin r) (b b' : Fin q), b ∈ I.takes i → b' ∈ I.takes i → b ≠ b' →
    ∀ (a : Fin (I.lectures b)) (a' : Fin (I.lectures b')), s ⟨b, a⟩ ≠ s ⟨b', a'⟩)

end CourseInstance

/-- A course scheduling problem with unavailabilities and preassignments (CSUP, §3.1, p. 157)
in `p` periods: a course scheduling instance together with
* `unavail b`, the set of periods at which course `K_b` cannot take place, and
* `pre l`, which is `some k̄` if lecture `l` has to be scheduled at period `k̄`, and `none` if
  lecture `l` is not preassigned. -/
structure CSUP (q r p : ℕ) extends CourseInstance q r where
  unavail : Fin q → Finset (Fin p)
  pre : (Σ b : Fin q, Fin (lectures b)) → Option (Fin p)

namespace CSUP

variable {q r p : ℕ}

/-- A solution of the CSUP in `p` periods: a feasible course schedule (§3.1) that respects every
unavailability and every preassignment. -/
def IsFeasible (P : CSUP q r p) (s : P.Lecture → Fin p) : Prop :=
  P.toCourseInstance.IsFeasibleSchedule p s ∧
  (∀ l : P.Lecture, s l ∉ P.unavail l.1) ∧
  (∀ (l : P.Lecture) (k : Fin p), P.pre l = some k → s l = k)

/-- Lecture-node `l` is joined to period-node `k` in `Ĝ` (proof of Proposition 3.1, pp. 157–158)
if course `K_b` of `l` cannot be scheduled at period `k`, or `l` has to be scheduled at a period
`k̄ ≠ k`. -/
def LecturePeriodAdj (P : CSUP q r p) (l : P.Lecture) (k : Fin p) : Prop :=
  k ∈ P.unavail l.1 ∨ ∃ kbar : Fin p, P.pre l = some kbar ∧ k ≠ kbar

/-- The adjacency relation of `Ĝ`. -/
def CsupAdj (P : CSUP q r p) : P.Lecture ⊕ Fin p → P.Lecture ⊕ Fin p → Prop
  | Sum.inl l, Sum.inl l' => P.Conflict l l'
  | Sum.inr k, Sum.inr k' => k ≠ k'
  | Sum.inl l, Sum.inr k => P.LecturePeriodAdj l k
  | Sum.inr k, Sum.inl l => P.LecturePeriodAdj l k

theorem csupAdj_symm (P : CSUP q r p) {x y : P.Lecture ⊕ Fin p} (h : P.CsupAdj x y) :
    P.CsupAdj y x := by
  rcases x with l | k <;> rcases y with l' | k'
  · exact P.toCourseInstance.conflict_symm h
  · exact h
  · exact h
  · exact fun e => h e.symm

theorem csupAdj_irrefl (P : CSUP q r p) (x : P.Lecture ⊕ Fin p) : ¬ P.CsupAdj x x := by
  rcases x with l | k
  · exact P.toCourseInstance.conflict_irrefl l
  · exact fun h => h rfl

/-- The graph `Ĝ` of the proof of Proposition 3.1 (pp. 157–158). Its nodes are the lecture-nodes
and one period-node for each period `k`. Two lecture-nodes are joined as in the graph of §3.1
(`CourseInstance.lectureGraph`); all pairs of period-nodes are joined; a lecture-node of course
`K_b` is joined to period-node `k` if `K_b` cannot be scheduled at period `k`; and a lecture that
has to be scheduled at period `k̄` is joined to every period-node `k ≠ k̄`. -/
def csupGraph (P : CSUP q r p) : SimpleGraph (P.Lecture ⊕ Fin p) where
  Adj := P.CsupAdj
  symm := ⟨fun _ _ h => P.csupAdj_symm h⟩
  loopless := ⟨P.csupAdj_irrefl⟩

end CSUP

/-- The embedding of the surviving nodes of `Ĝ′` into the nodes of `H` (Proposition 3.2): a
lecture-node that is not precoloured, or a period-node. -/
def survivorEmb {V : Type*} {p : ℕ} (pc : V → Option (Fin p)) :
    {v : V // pc v = none} ⊕ Fin p → V ⊕ Fin p
  | Sum.inl u => Sum.inl u.1
  | Sum.inr k => Sum.inr k

/-- The edges added when the precoloured nodes are removed (Proposition 3.2, via the proof of
Proposition 3.1): a surviving lecture-node `u` is joined to period-node `k` whenever `u` is
adjacent in `H` to a node `v` precoloured with the colour of period-node `k`. -/
def AddedEdge {V : Type*} {p : ℕ} (H : SimpleGraph (V ⊕ Fin p)) (pc : V → Option (Fin p)) :
    {v : V // pc v = none} ⊕ Fin p → {v : V // pc v = none} ⊕ Fin p → Prop
  | Sum.inl u, Sum.inr k => ∃ v : V, pc v = some k ∧ H.Adj (Sum.inl u.1) (Sum.inl v)
  | _, _ => False

/-- The graph `Ĝ′` of Proposition 3.2 (p. 158). `H` is a graph on lecture-nodes `V` and
period-nodes `Fin p`; `pc v = some k` means that lecture-node `v` is precoloured with the colour
of period-node `k`. `Ĝ′` is obtained by removing every precoloured node `v` and linking all its
(surviving) neighbours with the period-node `k` of its colour. Its nodes are the lecture-nodes
that are not precoloured and all period-nodes; its edges are the edges of `H` between surviving
nodes and the added edges. -/
def removePrecolored {V : Type*} {p : ℕ} (H : SimpleGraph (V ⊕ Fin p))
    (pc : V → Option (Fin p)) : SimpleGraph ({v : V // pc v = none} ⊕ Fin p) where
  Adj x y := H.Adj (survivorEmb pc x) (survivorEmb pc y) ∨ AddedEdge H pc x y ∨ AddedEdge H pc y x
  symm := by
    refine ⟨fun x y h => ?_⟩
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless := by
    refine ⟨fun x h => ?_⟩
    rcases h with h | h | h
    · exact H.irrefl h
    · rcases x with u | k <;> exact h
    · rcases x with u | k <;> exact h

end Timetabling85.CourseColoring



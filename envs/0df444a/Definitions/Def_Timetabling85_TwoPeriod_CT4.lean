-- Prove2me | Definitions.Def_Timetabling85_TwoPeriod_CT4
-- name    : Timetabling85_TwoPeriod_CT4
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:43.00198+00:00
-- url     : https://prove2.me/theorems/f5973c49-b06b-4b93-939e-2faf83a9c7d0
-- title:
--   §2.2, p. 154 — the daily class–teacher problem CT4, teacher schedules and the conflict graph
-- statement:
--   This file fixes the daily class–teacher problem with preassignments and unavailabilities of de Werra's §2.2, and the conflict graph built in the proof of Proposition 2.4.
--
--   **Data.** There are $m$ classes $c_1,\dots,c_m$, $n$ teachers $t_1,\dots,t_n$ and $p$ periods. For each class $c_i$ and teacher $t_j$, $\bar r_{ij}\in\mathbb N$ is the number of lectures of $c_i$ with $t_j$ that are not preassigned; $\bar b_{ik}\in\{0,1\}$ is $1$ exactly when class $c_i$ is available and not preassigned at period $k$; and $\bar c_{jk}\in\{0,1\}$ is $1$ exactly when teacher $t_j$ is available and not preassigned at period $k$.
--
--   **CT4.** A timetable is a $0/1$ array $\bar x_{ijk}$ ($\bar x_{ijk}=1$ if $c_i$ and $t_j$ meet at period $k$) with
--   $$
--   \sum_{k=1}^{p}\bar x_{ijk}=\bar r_{ij}\ (12),\qquad \sum_{j=1}^{n}\bar x_{ijk}\le \bar b_{ik}\ (13),\qquad \sum_{i=1}^{m}\bar x_{ijk}\le \bar c_{jk}\ (14),\qquad \bar x_{ijk}\in\{0,1\}\ (15).
--   $$
--
--   **Schedules of a teacher.** A possible schedule of $t_j$ is a $0/1$ array $y_{ik}$ (class $c_i$ meets $t_j$ at period $k$) satisfying the constraints that involve $t_j$ alone: $\sum_k y_{ik}=\bar r_{ij}$ for every $i$, $\sum_i y_{ik}\le \bar c_{jk}$ for every $k$, and $y_{ik}=1\Rightarrow \bar b_{ik}=1$. These form a finite set $\mathcal S_j$.
--
--   **Conflict graph.** Its nodes are the pairs $(j,y)$ with $y\in\mathcal S_j$. Two distinct nodes are linked when the schedules are not compatible: they are two different schedules of the same teacher, or they place the same class $c_i$ in the same period $k$.
--
--   These objects carry the reduction of the timetabling question to a stable-set question used in the proof of Proposition 2.4.
--
--   **Formalization Note** $\bar r,\bar b,\bar c$ are taken as data; the preassignments $p_{ijk}$ only produce them. $0/1$ values are Booleans and are summed through `Bool.toNat`. Classes, teachers and periods are indexed by `Fin m`, `Fin n`, `Fin p`. The conflict graph is `SimpleGraph.fromRel` of the incompatibility relation, so a node is never linked to itself.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), p. 154, §2.2, constraints CT4 (12)–(15) and the definitions of r̄_ij, b̄_ik, c̄_jk; p. 155, proof of Proposition 2.4 (the graph G)

import Mathlib

namespace Timetabling85.TwoPeriod

/-- The data of the daily class–teacher problem CT4 with preassignments and unavailabilities
(de Werra 1985, §2.2, p. 154): `m` classes, `n` teachers, `p` periods,
`rbar i j` = r̄_ij (lectures of class `i` with teacher `j` still to schedule),
`bbar i k` = b̄_ik (class `i` available and not preassigned at period `k`),
`cbar j k` = c̄_jk (teacher `j` available and not preassigned at period `k`). -/
structure CT4Data (m n p : ℕ) where
  rbar : Fin m → Fin n → ℕ
  bbar : Fin m → Fin p → Bool
  cbar : Fin n → Fin p → Bool

/-- `x i j k = true` encodes x̄_ijk = 1; the Boolean type encodes constraint (15).
`IsSolution I x` is constraints (12)–(14) of CT4. -/
def IsSolution {m n p : ℕ} (I : CT4Data m n p) (x : Fin m → Fin n → Fin p → Bool) : Prop :=
  (∀ i j, (∑ k, (x i j k).toNat) = I.rbar i j) ∧
  (∀ i k, (∑ j, (x i j k).toNat) ≤ (I.bbar i k).toNat) ∧
  (∀ j k, (∑ i, (x i j k).toNat) ≤ (I.cbar j k).toNat)

/-- A schedule of teacher `t_j`: an assignment `y i k` (class `i` meets `t_j` at period `k`)
satisfying the parts of (12)–(15) that involve `t_j` alone: (12) for `j`, (14) for `j`, and
class availability `y i k → b̄_ik` from (13). -/
def IsTeacherSchedule {m n p : ℕ} (I : CT4Data m n p) (j : Fin n)
    (y : Fin m → Fin p → Bool) : Prop :=
  (∀ i, (∑ k, (y i k).toNat) = I.rbar i j) ∧
  (∀ k, (∑ i, (y i k).toNat) ≤ (I.cbar j k).toNat) ∧
  (∀ i k, y i k = true → I.bbar i k = true)

instance {m n p : ℕ} (I : CT4Data m n p) (j : Fin n) :
    DecidablePred (IsTeacherSchedule I j) := fun y => by
  unfold IsTeacherSchedule; infer_instance

/-- The finite set of possible schedules of teacher `t_j`. -/
def schedules {m n p : ℕ} (I : CT4Data m n p) (j : Fin n) :
    Finset (Fin m → Fin p → Bool) :=
  Finset.univ.filter (IsTeacherSchedule I j)

/-- A node of the conflict graph: a teacher together with one of its possible schedules. -/
abbrev Node {m n p : ℕ} (I : CT4Data m n p) : Type :=
  Σ j : Fin n, {y : Fin m → Fin p → Bool // y ∈ schedules I j}

/-- The conflict graph `G` of the proof of Proposition 2.4 (p. 155): two distinct nodes are
linked iff the corresponding schedules are not compatible, i.e. they are two different schedules
of the same teacher, or they put the same class in the same period. -/
def conflictGraph {m n p : ℕ} (I : CT4Data m n p) : SimpleGraph (Node I) :=
  SimpleGraph.fromRel fun u v =>
    u.1 = v.1 ∨ ∃ i k, u.2.1 i k = true ∧ v.2.1 i k = true

end Timetabling85.TwoPeriod



-- Prove2me | Definitions.Def_CriticalPath_Events_ProjectNetwork
-- name    : CriticalPath_Events_ProjectNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:24:46.002382+00:00
-- url     : https://prove2.me/theorems/b2f8c67b-da65-4f5a-a868-a9c774023bd9
-- title:
--   Project network: events 0..n, jobs (i, j) with i < j, origin precedes and terminus follows every event
-- statement:
--   A **project network** in the sense of Kelley and Walker models a project as a directed graph whose arrows are the *jobs* and whose nodes are the *events* (the junctions where arrows meet).
--
--   Fix $n \ge 1$. The project $P$ has $n+1$ events labelled $0, 1, \dots, n$; event $0$ is the **origin** and event $n$ the **terminus**. A job is an arrow from event $i$ to event $j$ and is called job $(i,j)$; the set of jobs is a finite set $P \subseteq \{0,\dots,n\}^2$. The data satisfy:
--
--   1. **Labelling.** The event at the head of an arrow has a larger label than the event at the tail: $i < j$ for every $(i,j) \in P$.
--   2. **Origin precedes every event.** For every event $k$ there is a chain of jobs $0 = v_0 \to v_1 \to \dots \to v_r = k$ with $r \ge 0$ and every $(v_{s-1}, v_s) \in P$.
--   3. **Terminus follows every event.** For every event $k$ there is a chain of jobs from $k$ to $n$.
--
--   From these data one reads off, for each event $j$, the set of events $i$ with $(i,j) \in P$ (its predecessors) and, for each event $i$, the set of events $j$ with $(i,j)\in P$ (its successors). Every event other than the origin has at least one predecessor, and every event other than the terminus has at least one successor.
--
--   This is the combinatorial model underlying the earliest and latest event times, critical jobs and critical paths of the Critical-Path Method.
--
--   **Formalization Note** Events are `Fin (n + 1)`, origin `0`, terminus `Fin.last n`. A job is an ordered pair of events, so there is at most one job per ordered pair, as the paper's name "job $(i,j)$" implies. Chains of jobs are expressed with `Relation.ReflTransGen` of the relation "$(i,j) \in P$". The file also proves the two nonemptiness facts above, which the recursions (1) and (2) need.
-- source:
--   Kelley, Walker, Critical-Path Planning and Scheduling, Proc. Eastern Joint Computer Conf. 1959, pp. 161-162, Part I §1 Project Structure ("These relations of order can be shown graphically" to "then the associated job is called job (i, j)")

import Mathlib

namespace CriticalPath.Events

/-- A project network in the sense of Kelley–Walker (1959), Part I §1, pp. 161–162:
`n + 1` events labelled `0, …, n` (origin `0`, terminus `n`, two distinguished events so `1 ≤ n`),
jobs `(i, j)` given as a finite set `P` of ordered pairs of events, every job's head having a
larger label than its tail, and origin preceding and terminus following every event. -/
structure ProjectNetwork (n : ℕ) where
  /-- The jobs of the project: job `(i, j)` is an arrow from event `i` to event `j`. -/
  P : Finset (Fin (n + 1) × Fin (n + 1))
  /-- There are two distinguished events, origin `0` and terminus `n`. -/
  one_le : 1 ≤ n
  /-- The event at the head of an arrow has a larger label than the event at the tail. -/
  label_lt : ∀ e ∈ P, e.1 < e.2
  /-- Origin precedes every event. -/
  origin_precedes : ∀ k, Relation.ReflTransGen (fun i j => (i, j) ∈ P) 0 k
  /-- Terminus follows every event. -/
  terminus_follows : ∀ k, Relation.ReflTransGen (fun i j => (i, j) ∈ P) k (Fin.last n)

namespace ProjectNetwork

variable {n : ℕ} (N : ProjectNetwork n)

/-- The events `i` with a job `(i, j)` ending at `j`. -/
def pred (j : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => (i, j) ∈ N.P)

/-- The events `j` with a job `(i, j)` starting at `i`. -/
def succ (i : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun j => (i, j) ∈ N.P)

theorem mem_pred {i j : Fin (n + 1)} : i ∈ N.pred j ↔ (i, j) ∈ N.P := by
  simp [pred]

theorem mem_succ {i j : Fin (n + 1)} : j ∈ N.succ i ↔ (i, j) ∈ N.P := by
  simp [succ]

theorem pred_nonempty {j : Fin (n + 1)} (h : j ≠ 0) : (N.pred j).Nonempty := by
  rcases (N.origin_precedes j).cases_tail with h0 | ⟨b, _, hb⟩
  · exact absurd h0 h
  · exact ⟨b, (N.mem_pred).2 hb⟩

theorem succ_nonempty {i : Fin (n + 1)} (h : i ≠ Fin.last n) : (N.succ i).Nonempty := by
  rcases (N.terminus_follows i).cases_head with h0 | ⟨b, hb, _⟩
  · exact absurd h0 h
  · exact ⟨b, (N.mem_succ).2 hb⟩

theorem lt_of_mem_pred {i j : Fin (n + 1)} (h : i ∈ N.pred j) : i < j :=
  N.label_lt (i, j) ((N.mem_pred).1 h)

theorem lt_of_mem_succ {i j : Fin (n + 1)} (h : j ∈ N.succ i) : i < j :=
  N.label_lt (i, j) ((N.mem_succ).1 h)

end ProjectNetwork

end CriticalPath.Events



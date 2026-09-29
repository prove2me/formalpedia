-- Prove2me | Definitions.Def_CriticalPath_CostCurve_ProjectNetwork
-- name    : CriticalPath_CostCurve_ProjectNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:28:48.340733+00:00
-- url     : https://prove2.me/theorems/86ec22fa-33e9-480d-a74a-c1e1e3771f5c
-- title:
--   Project network: events 0..n, jobs (i, j) with i < j, origin precedes and terminus follows every event
-- statement:
--   A **project network** (activity-on-arrow project diagram) consists of $n+1$ events labelled $0, 1, \dots, n$ with $n \ge 1$, and a finite set $P$ of jobs. A job is an ordered pair $(i,j) \in P$, an arrow from event $i$ to event $j$; there is at most one job per ordered pair. The data satisfy the standing assumptions of the paper:
--
--   1. the head of every arrow has a larger label than its tail: $(i,j) \in P \Rightarrow i < j$;
--   2. the origin $0$ precedes every event: every event $k$ is reachable from $0$ along a (possibly empty) directed path of jobs;
--   3. the terminus $n$ follows every event: $n$ is reachable from every event $k$ along such a path.
--
--   These are the objects on which the earliest event times, schedules and the project cost curve of Kelley and Walker are defined.
--
--   **Formalization Note** Events are `Fin (n + 1)`, the origin is `0` and the terminus is `Fin.last n`; reachability is `Relation.ReflTransGen` of the arrow relation. The field `one_le : 1 ≤ n` records that origin and terminus are two distinct events.
-- source:
--   Kelley, Walker, Critical-Path Planning and Scheduling, Proc. Eastern Joint Computer Conf. 1959, DOI 10.1145/1460299.1460318, pp. 161-162, Part I §1 Project Structure (events, origin and terminus, labelling of events)

import Mathlib

namespace CriticalPath.CostCurve

/-- A project network in the sense of Kelley–Walker (1959), Part I §1, pp. 161–162.
Events are labelled `0, 1, …, n` (`Fin (n + 1)`); origin is `0` and terminus is `Fin.last n`.
Jobs are arrows `(i, j) ∈ P`, at most one per ordered pair. -/
structure ProjectNetwork (n : ℕ) where
  /-- The set of jobs `(i, j)`: an arrow from event `i` to event `j`. -/
  P : Finset (Fin (n + 1) × Fin (n + 1))
  /-- Origin and terminus are two distinct events. -/
  one_le : 1 ≤ n
  /-- The head of an arrow always has a larger label than its tail. -/
  label_lt : ∀ e ∈ P, e.1 < e.2
  /-- Origin precedes every event. -/
  origin_precedes : ∀ k : Fin (n + 1), Relation.ReflTransGen (fun i j => (i, j) ∈ P) 0 k
  /-- Terminus follows every event. -/
  terminus_follows : ∀ k : Fin (n + 1),
    Relation.ReflTransGen (fun i j => (i, j) ∈ P) k (Fin.last n)

end CriticalPath.CostCurve



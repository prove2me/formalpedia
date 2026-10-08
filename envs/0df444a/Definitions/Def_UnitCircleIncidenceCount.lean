-- Prove2me | Definitions.Def_UnitCircleIncidenceCount
-- name    : UnitCircleIncidenceCount
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T17:28:49.699441+00:00
-- url     : https://prove2.me/theorems/557ba202-f286-42e2-8c12-63917104f718
-- title:
--   Unit Circle Incidence Count
-- statement:
--   For a finite set $P\subset\mathbb{R}^2$, $\operatorname{UnitCircleIncidenceCount}(P)$ is the number of ordered pairs $(p,q)\in P\times P$ such that $q$ lies on the unit circle centered at $p$. This is the formal version of the paper's sum $\sum_{p\in P} r_p$, where $r_p=|P\cap C_p|$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `UnitCircleIncidenceCount`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/UnitCircleIncidenceCount.lean#L1-L9

import Definitions.Def_UnitCircle

open Classical
noncomputable section

-- [TABLET NODE: UnitCircleIncidenceCount]
noncomputable def UnitCircleIncidenceCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
-- BODY
  ((P.product P).filter (fun pq => pq.2 ∈ UnitCircle pq.1)).card



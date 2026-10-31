-- Prove2me | Definitions.Def_ReservationPolicy_Benchmark
-- name    : ReservationPolicy_Benchmark
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:20.624036+00:00
-- url     : https://prove2.me/theorems/2b604c6a-440b-45e8-bfd9-05c5c592f1fd
-- title:
--   Outcome without the policy
-- statement:
--   An outcome of the game without the policy records the effort $e_x$ of type-$x$ students, the effort $e_y$ of type-$y$ students, the common cutoff $d$, and the rewards $r_x,r_y$ of admitted students of each type. The paper restricts attention to pure strategies that are symmetric within a type.
--
--   **Formalization Note** The investment decision is not a field: the predicates `IsInvestBenchmark` and `IsNoInvestBenchmark` fix it.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), §2–§3, pp.9–13

import Mathlib

namespace ReservationPolicy

/-- An outcome of the game without the policy: the efforts `ex`, `ey` of the two types, the common
cutoff `d` and the rewards `rx`, `ry`. Strategies are pure and symmetric within a type (p.12,
footnote 22, p.35). Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), §2–§3, pp.9–13 (PDF 9–13). -/
@[ext] structure Benchmark where
  ex : ℝ
  ey : ℝ
  d : ℝ
  rx : ℝ
  ry : ℝ

end ReservationPolicy



-- Prove2me | Definitions.Def_SybilClinch_Run
-- name    : SybilClinch_Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:08.001349+00:00
-- url     : https://prove2.me/theorems/5630463c-c5ba-47f1-b200-16072b66940e
-- title:
--   Data of a clinching run: terminal price and allocation paths
-- statement:
--   One execution of a target-based clinching auction uses the clock price as time. Its data are the terminal clock price $p_f$ and, for each identity $i$, the cumulative allocation path $p\mapsto x_i(p)$, the quantity of $X$ received through clock price $p$ after all events at $p$. Payments, effective budgets, the target and the water level are derived from these paths; `IsRun` states when the data form a run.
--
--   **Formalization Note** Allocation paths are nondecreasing right-continuous (Stieltjes) functions, so fixed-price purchases are jumps. The terminal price is finite.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2–§3.5, pp.9–12 (PDF pp.11–14)

import Mathlib

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2–§3.5, printed pp.9–12 (PDF pp.11–14): the data of one execution of a (target-based)
clinching auction, with the clock price as time variable: the terminal clock price `pf` and, for
each identity, its cumulative allocation path `x i`, as a function of the clock price.

`x i p` is the allocation received through clock price `p`, after all events at `p` have been
processed. Payments, budgets, the target and the water level are derived from these paths
(`Run.pay`, `Run.bud`, `Run.resid`, `Run.waterLevel`); the conditions that make the data a run of a
given mechanism and profile are `IsRun`.

**Formalization Note.** Allocation paths are Stieltjes functions (nondecreasing, right-continuous),
so `dxᵢ ≥ 0` and fixed-price purchases are jumps. The terminal price is finite: a completed run
terminates. -/
structure Run where
  /-- The terminal clock price `p_f`. -/
  pf : ℝ
  /-- The cumulative allocation path `p ↦ xᵢ(p)` of each identity. -/
  x : ℕ → StieltjesFunction ℝ

end SybilClinch



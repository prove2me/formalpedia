-- Prove2me | Definitions.Def_SupplierLearning_outcomeValue
-- name    : SupplierLearning_outcomeValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:42:42.680889+00:00
-- url     : https://prove2.me/theorems/1aa0fe16-d3b6-4b1a-8216-58f4c269a61f
-- title:
--   The learning outcome $\Lambda$ as a number
-- statement:
--   The numeric value of the learning outcome: $\Lambda\in\{0,1\}$ is represented by a Boolean, with `true` standing for $\Lambda=1$ and `false` for $\Lambda=0$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, p.6, Table 1

import Mathlib

namespace SupplierLearning

/-- **The learning outcome Λ as a number.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, p.6, Table 1 (PDF p.6).

**Formalization Note.** `Λ` is a `Bool`: `true` is `Λ = 1`, `false` is `Λ = 0`. -/
noncomputable def outcomeValue : Bool → ℝ
  | true => 1
  | false => 0

end SupplierLearning



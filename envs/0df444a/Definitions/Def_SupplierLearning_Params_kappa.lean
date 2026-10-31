-- Prove2me | Definitions.Def_SupplierLearning_Params_kappa
-- name    : SupplierLearning_Params_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:43:23.576027+00:00
-- url     : https://prove2.me/theorems/fa746c10-0ec8-4d25-b597-5daa12bc80f1
-- title:
--   The odds ratio $\kappa=\nu/(1-\nu)$
-- statement:
--   The abbreviation $\kappa=\nu/(1-\nu)$, the factor by which the rent paid to type $\ell$ enters the type-$h$ problem.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, note 9, p.26

import Definitions.Def_SupplierLearning_Params

namespace SupplierLearning

/-- **The odds ratio κ=ν/(1-ν).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, note 9, p.26 (PDF p.26).

**Formalization Note.** An abbreviation for the factor `ν/(1 − ν)` that appears throughout the proof. `Params.Standing` makes the denominator positive. -/
noncomputable def Params.kappa (P : Params) : ℝ := P.ν / (1 - P.ν)

end SupplierLearning



-- Prove2me | Definitions.Def_SupplierLearning_Params_expectOutcome
-- name    : SupplierLearning_Params_expectOutcome
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:43:23.82924+00:00
-- url     : https://prove2.me/theorems/4973a575-af8a-42eb-a74f-95fdfeca4b7c
-- title:
--   Expectation $\mathbb E_\Lambda$ over the learning outcome
-- statement:
--   The expectation over the Bernoulli($\rho$) learning outcome: $\mathbb E_\Lambda[g(\Lambda)]=\rho\,g(1)+(1-\rho)\,g(0)$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, p.6, Table 1; App. p.5

import Definitions.Def_SupplierLearning_Params

namespace SupplierLearning

/-- **Expectation \mathbb E_Λ over the learning outcome.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, p.6, Table 1; App. p.5 (PDF p.6, 37).

**Formalization Note.** `E_Λ[g(Λ)] = ρ g(1) + (1 − ρ) g(0)`, the two-term sum the appendix writes out on App. p.5. -/
noncomputable def Params.expectOutcome (P : Params) (g : Bool → ℝ) : ℝ :=
  P.ρ * g true + (1 - P.ρ) * g false

end SupplierLearning



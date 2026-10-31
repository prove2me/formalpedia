-- Prove2me | Definitions.Def_SupplierLearning_Params_printedContract
-- name    : SupplierLearning_Params_printedContract
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:48:45.202408+00:00
-- url     : https://prove2.me/theorems/0f204929-fa70-498b-8301-a8b284a709e4
-- title:
--   The printed contract $\phi^{\mathrm{AL}}$
-- statement:
--   The contract of Proposition 1 as printed, for type-$h$ quantities $(q,y,z)$: type $\ell$ receives the printed term at the first-best quantities with rent $U^\ell(q,y,z)$ of (4), and type $h$ the deferred payment term (19).
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Proposition 1, p.13

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_rent
import Definitions.Def_SupplierLearning_Params_deferredTerm
import Definitions.Def_SupplierLearning_Params_printedLowTerm

namespace SupplierLearning

/-- **The printed contract φ^{AL}.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Proposition 1, p.13 (PDF p.13).

**Formalization Note.** `Params.contractStar` with type ℓ's printed payment. -/
noncomputable def Params.printedContract (P : Params) (q y z : ℝ) : Contract
  | .l => P.printedLowTerm (P.rent q y z)
  | .h => P.deferredTerm q y z

end SupplierLearning



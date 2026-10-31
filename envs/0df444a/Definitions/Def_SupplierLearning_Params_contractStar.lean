-- Prove2me | Definitions.Def_SupplierLearning_Params_contractStar
-- name    : SupplierLearning_Params_contractStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:53.496513+00:00
-- url     : https://prove2.me/theorems/0fa9cee2-69f9-40bc-b708-b8e4a6c095cd
-- title:
--   The contract $\phi^*$
-- statement:
--   The contract $\phi^*$ for type-$h$ quantities $(q,y,z)$: type $\ell$ receives the corrected term at the first-best quantities with rent $U^\ell(q,y,z)$ of (4), and type $h$ the deferred payment term (19).
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Proposition 1, p.13, with correction C1

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_rent
import Definitions.Def_SupplierLearning_Params_deferredTerm
import Definitions.Def_SupplierLearning_Params_correctedLowTerm

namespace SupplierLearning

/-- **The contract φ^*.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Proposition 1, p.13, with correction C1 (PDF p.13).

**Formalization Note.** Type ℓ gets its first best with the corrected payment and rent (4); type h gets the deferred payment (19). -/
noncomputable def Params.contractStar (P : Params) (q y z : ℝ) : Contract
  | .l => P.correctedLowTerm (P.rent q y z)
  | .h => P.deferredTerm q y z

end SupplierLearning



-- Prove2me | Definitions.Def_SupplierLearning_Contract
-- name    : SupplierLearning_Contract
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:43:50.256107+00:00
-- url     : https://prove2.me/theorems/3baea7e4-8a23-4545-8bcb-80d883cd7c29
-- title:
--   A two-period contract $\phi$ (direct mechanism)
-- statement:
--   A two-period contract $\phi\equiv\{(p_t^s,q_t^s)\}_{t,s}$ for $t=1,2$ and each information state $s$. By the revelation principle (p.8) the buyer focuses on direct mechanisms, so a contract is a menu with one term per reported type.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, pp.7–8

import Definitions.Def_SupplierLearning_SupplierType
import Definitions.Def_SupplierLearning_Term

namespace SupplierLearning

/-- **A two-period contract φ (direct mechanism).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, pp.7–8 (PDF p.7, 8).

**Formalization Note.** A direct revelation mechanism, as on p.8: one `Term` per reported type. -/
abbrev Contract := SupplierType → Term

end SupplierLearning



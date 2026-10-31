-- Prove2me | Definitions.Def_SupplierLearning_Params_B
-- name    : SupplierLearning_Params_B
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:43:36.005638+00:00
-- url     : https://prove2.me/theorems/77e2e962-f37d-4afe-bdc0-908678ef1e4d
-- title:
--   The rate $B=(r^h-\nu r^\ell)/(1-\nu)$
-- statement:
--   The abbreviation $B=(r^h-\nu r^\ell)/(1-\nu)$. Under the standing assumptions, $B>0$ is exactly the paper's condition $r^h>\nu r^\ell$, and under single deviation $\bar y(q)-\bar z(q)=qB/2$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 3, (A1)–(A3), App. p.7

import Definitions.Def_SupplierLearning_Params

namespace SupplierLearning

/-- **The rate B=(r^h-ν r^ℓ)/(1-ν).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 3, (A1)–(A3), App. p.7 (PDF p.39).

**Formalization Note.** An abbreviation, not named in the paper. `B > 0` is the paper's condition `r^h > ν r^ℓ`. -/
noncomputable def Params.B (P : Params) : ℝ := (P.rh - P.ν * P.rl) / (1 - P.ν)

end SupplierLearning



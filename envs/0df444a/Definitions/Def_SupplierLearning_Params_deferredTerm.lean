-- Prove2me | Definitions.Def_SupplierLearning_Params_deferredTerm
-- name    : SupplierLearning_Params_deferredTerm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:43:52.949571+00:00
-- url     : https://prove2.me/theorems/043b0895-3430-4d38-9d5d-c5e9feebf442
-- title:
--   The deferred payment term of type $h$, eq. (19)
-- statement:
--   The deferred payment term for type $h$ at quantities $(q,y,z)$:
--   $$
--   p_1^h=c^hq-\delta\rho r^hqz,\qquad p_2^{h0}=c^hz,\qquad p_2^{h1}=(c^h-r^hq)y+r^hqz.
--   $$
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, eq. (19), App. p.6; Proposition 1(a), p.13

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Term

namespace SupplierLearning

/-- **The deferred payment term of type h, eq. (19).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, eq. (19), App. p.6; Proposition 1(a), p.13 (PDF p.38, 13).

**Formalization Note.** The quantities `(q, y, z)` are arguments. -/
noncomputable def Params.deferredTerm (P : Params) (q y z : ℝ) : Term where
  p₁ := P.ch * q - P.δ * P.ρ * P.rh * q * z
  q₁ := q
  p₂ := fun
    | true => (P.ch - P.rh * q) * y + P.rh * q * z
    | false => P.ch * z
  q₂ := fun
    | true => y
    | false => z

end SupplierLearning



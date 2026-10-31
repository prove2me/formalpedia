-- Prove2me | Definitions.Def_SupplierLearning_Params_Candidate
-- name    : SupplierLearning_Params_Candidate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:49.759718+00:00
-- url     : https://prove2.me/theorems/7204f6c2-de1c-4ef5-8efa-3e9d45fe065b
-- title:
--   Candidate type-$h$ quantities (hypothesis E4)
-- statement:
--   The triple $(q,y,z)$ is a **candidate** for type $h$'s quantities when
--
--   1. $0\le q$, $0\le z$, $0<q+y$, and $(r^h-r^\ell)q\le\Delta c_1$;
--   2. $(y,z)=(\bar y(q),\bar z(q))$ if $\bar y(q)>\bar z(q)$, and $y=z=\hat y(q)$ otherwise;
--   3. $G(q,y)=0$ if $r^hq>\Delta c_1$; $G(q,y)+g(y,z)=0$ if $r^hq<\Delta c_1$; and $G(q,y)\le0\le G(q,y)+g(y,z)$ if $r^hq=\Delta c_1$.
--
--   **Formalization Note** The conditions in 1 exclude corner optima, where the printed formulas are false. The one-sided condition in 3 replaces the printed first-order equation at the kink, where $\partial U^\ell/\partial q_1^h$ does not exist.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Proposition 1(b), p.13; proof, Steps 2–3, App. pp.6–8

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_separatingHigh
import Definitions.Def_SupplierLearning_Params_separatingLow
import Definitions.Def_SupplierLearning_Params_poolingQuantity
import Definitions.Def_SupplierLearning_Params_slopeRight
import Definitions.Def_SupplierLearning_Params_slopeGap

namespace SupplierLearning

/-- **Candidate type-h quantities (hypothesis E4).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Proposition 1(b), p.13; proof, Steps 2–3, App. pp.6–8 (PDF p.13, 38–40).

**Formalization Note.** This pins `(q, y, z)` down by the first-order conditions and the separating or pooling rule of Proposition 1(b). The bounds are correction C3, the separating forms correction C4, and the one-sided inequalities at the kink correction C5. -/
structure Params.Candidate (P : Params) (q y z : ℝ) : Prop where
  q_nonneg : 0 ≤ q
  z_nonneg : 0 ≤ z
  pos : 0 < q + y
  capacity : (P.rh - P.rl) * q ≤ P.ch - P.cl
  period_two :
    (P.separatingLow q < P.separatingHigh q ∧ y = P.separatingHigh q ∧ z = P.separatingLow q) ∨
    (P.separatingHigh q ≤ P.separatingLow q ∧ y = P.poolingQuantity q ∧ z = P.poolingQuantity q)
  slope_above : P.ch - P.cl < P.rh * q → P.slopeRight q y = 0
  slope_below : P.rh * q < P.ch - P.cl → P.slopeRight q y + P.slopeGap y z = 0
  slope_kink : P.rh * q = P.ch - P.cl →
    P.slopeRight q y ≤ 0 ∧ 0 ≤ P.slopeRight q y + P.slopeGap y z

end SupplierLearning



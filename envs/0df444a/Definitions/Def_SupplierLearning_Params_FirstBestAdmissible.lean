-- Prove2me | Definitions.Def_SupplierLearning_Params_FirstBestAdmissible
-- name    : SupplierLearning_Params_FirstBestAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:33.924982+00:00
-- url     : https://prove2.me/theorems/3ec2237c-c8e6-4bd6-953d-cdb9cfd03ff3
-- title:
--   The first best of type $\ell$ is admissible (hypothesis E2)
-- statement:
--   Type $\ell$'s first best lies in the admissible set: $q_1^{\ell|\mathrm{PP}}\ge0$, $q_2^{\ell0|\mathrm{PP}}\ge0$, and $(r^h-r^\ell)\,q_1^{\ell|\mathrm{PP}}\le\Delta c_1$.
--
--   **Formalization Note** The printed proposition assumes neither nonnegativity nor (C) at the optimum. At the Fig. 7 parameters with $r^h=0.9$ and $a_1=80$, the printed first-order condition gives $q_1^h\approx40.04$ while $Q=15$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, correction of Proposition 1, p.13; (C), p.7

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_firstBestOne
import Definitions.Def_SupplierLearning_Params_firstBestTwo

namespace SupplierLearning

/-- **The first best of type ℓ is admissible (hypothesis E2).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, correction of Proposition 1, p.13; (C), p.7 (PDF p.13, 7).

**Formalization Note.** Not in the printed proposition; correction C3. (C) applies to every first-period quantity, so it has to hold at type ℓ's first best too. -/
structure Params.FirstBestAdmissible (P : Params) : Prop where
  q₁_nonneg : 0 ≤ P.firstBestOne .l
  q₂_nonneg : 0 ≤ P.firstBestTwo .l false
  capacity : (P.rh - P.rl) * P.firstBestOne .l ≤ P.ch - P.cl

end SupplierLearning



-- Prove2me | Definitions.Def_SupplierLearning_Params_printedLowTerm
-- name    : SupplierLearning_Params_printedLowTerm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:11.532986+00:00
-- url     : https://prove2.me/theorems/bc733485-be22-434c-a221-5633bdafbe30
-- title:
--   The printed term of type $\ell$
-- statement:
--   The term of type $\ell$ at the first-best quantities with rent $u$, exactly as printed in Proposition 1(a):
--   $$
--   p_1^\ell=c^\ell q^\ell-\delta\rho r^\ell q^\ell z^\ell+u,\quad p_2^{\ell1}=(c^\ell-r^\ell q^\ell)y^\ell+r^\ell q^\ell z^\ell,\quad p_2^{\ell0}=c^\ell z^\ell.
--   $$
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Proposition 1(a), p.13

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Term
import Definitions.Def_SupplierLearning_Params_firstBestOne
import Definitions.Def_SupplierLearning_Params_firstBestTwo

namespace SupplierLearning

/-- **The printed term of type ℓ.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Proposition 1(a), p.13 (PDF p.13).

**Formalization Note.** The payment exactly as printed, with `θ = ℓ`. It is kept for clause 5 of the goal. -/
noncomputable def Params.printedLowTerm (P : Params) (u : ℝ) : Term where
  p₁ := P.cl * P.firstBestOne .l -
    P.δ * P.ρ * P.rl * P.firstBestOne .l * P.firstBestTwo .l false + u
  q₁ := P.firstBestOne .l
  p₂ := fun
    | true => (P.cl - P.rl * P.firstBestOne .l) * P.firstBestTwo .l true +
        P.rl * P.firstBestOne .l * P.firstBestTwo .l false
    | false => P.cl * P.firstBestTwo .l false
  q₂ := fun Λ => P.firstBestTwo .l Λ

end SupplierLearning



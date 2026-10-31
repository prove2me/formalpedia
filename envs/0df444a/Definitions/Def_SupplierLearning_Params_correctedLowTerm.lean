-- Prove2me | Definitions.Def_SupplierLearning_Params_correctedLowTerm
-- name    : SupplierLearning_Params_correctedLowTerm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:48:14.571881+00:00
-- url     : https://prove2.me/theorems/c99da2f9-48cf-4480-9702-e2823e16482d
-- title:
--   The corrected term of type $\ell$
-- statement:
--   The term of type $\ell$ at the first-best quantities $(q^\ell,y^\ell,z^\ell)$ with rent $u$, in corrected form:
--   $$
--   p_1^\ell=c^\ell q^\ell-\delta\rho r^\ell q^\ell y^\ell+u,\quad p_2^{\ell1}=(c^\ell-r^\ell q^\ell)y^\ell+r^\ell q^\ell y^\ell,\quad p_2^{\ell0}=c^\ell z^\ell.
--   $$
--
--   **Formalization Note** The page has $q_2^{\ell0}$ where this has $y^\ell$ in the two learning terms. The printed payment can violate (IC$^h$): at $a_1=a_2=100$, $c^\ell=10$, $c^h=11$, $r^\ell=r^h=1$, $\delta=\rho=\nu=1/2$ it gives $\tilde U(h;\ell)=49/10>0=U(h)$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, correction C1 of Proposition 1(a), p.13

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Term
import Definitions.Def_SupplierLearning_Params_firstBestOne
import Definitions.Def_SupplierLearning_Params_firstBestTwo

namespace SupplierLearning

/-- **The corrected term of type ℓ.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, correction C1 of Proposition 1(a), p.13 (PDF p.13).

**Formalization Note.** The printed shape with `q₂^{ℓ0}` replaced by `q₂^{ℓ1}` in the two learning terms, so that (IC^{ℓ0}) binds in place of (IC^{ℓ1}). Quantities are the first best. `u` is the rent. -/
noncomputable def Params.correctedLowTerm (P : Params) (u : ℝ) : Term where
  p₁ := P.cl * P.firstBestOne .l -
    P.δ * P.ρ * P.rl * P.firstBestOne .l * P.firstBestTwo .l true + u
  q₁ := P.firstBestOne .l
  p₂ := fun
    | true => (P.cl - P.rl * P.firstBestOne .l) * P.firstBestTwo .l true +
        P.rl * P.firstBestOne .l * P.firstBestTwo .l true
    | false => P.cl * P.firstBestTwo .l false
  q₂ := fun Λ => P.firstBestTwo .l Λ

end SupplierLearning



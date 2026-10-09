-- Prove2me | Definitions.Def_actuarial_temporaryAnnuityImmediatePV
-- name    : actuarial_temporaryAnnuityImmediatePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T20:05:41.996909+00:00
-- url     : https://prove2.me/theorems/f405c5a6-1231-4889-8559-7c30897e6474
-- title:
--   Temporary life annuity payable in arrears
-- statement:
--   The present value of a temporary annuity payable in arrears is the sum of unit payments at the ends of years one through the term, each discounted to the present and payable only if the life survives to that payment date.
--
--   $$
--   Z_{\mathrm{immediate}}=\sum_{k=0}^{n-1}v^{k+1}\mathbf1_{\{K\ge k+1\}}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.2, equation (3.16), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_presentValue
import Definitions.Def_actuarial_curtateSurvivalEvent

namespace ActuarialValuation

noncomputable def temporaryAnnuityImmediatePV {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  presentValue (Finset.range n) (fun k : ℕ => k + 1)
    (fun t : ℕ => v ^ t) (fun _ : ℕ => (1 : ℝ))
    (fun k : ℕ => curtateSurvivalEvent K (k + 1)) ω

end ActuarialValuation



-- Prove2me | Definitions.Def_actuarial_temporaryAnnuityDuePV
-- name    : actuarial_temporaryAnnuityDuePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T20:04:45.687432+00:00
-- url     : https://prove2.me/theorems/96e5de0e-faa0-4aa9-b754-c30d73a54d20
-- title:
--   Temporary life annuity payable in advance
-- statement:
--   The present value of a temporary annuity payable in advance is the sum of unit payments at times zero through one year before the term ends, each discounted to the present and payable only if the life has survived to that time. The payment at time zero is therefore made without a prior survival requirement.
--
--   $$
--   Z_{\mathrm{due}}=\sum_{k=0}^{n-1}v^k\mathbf1_{\{K\ge k\}}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.2, equation (3.15), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_presentValue
import Definitions.Def_actuarial_curtateSurvivalEvent

namespace ActuarialValuation

noncomputable def temporaryAnnuityDuePV {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  presentValue (Finset.range n) (fun k : ℕ => k)
    (fun t : ℕ => v ^ t) (fun _ : ℕ => (1 : ℝ))
    (curtateSurvivalEvent K) ω

end ActuarialValuation



-- Prove2me | Definitions.Def_actuarial_guaranteedAnnuityImmediatePV
-- name    : actuarial_guaranteedAnnuityImmediatePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T21:30:08.304332+00:00
-- url     : https://prove2.me/theorems/b3b4b4d4-09d3-450d-9471-619d937a11e0
-- title:
--   Guaranteed annuity immediate pv
-- statement:
--   Defines an immediate annuity whose payments are certain from time one through the guaranteed term, then continue while the lifetime condition holds. A zero term gives the whole-life annuity immediate.
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{guaranteed,immediate}}=\sum_{k=0}^{\max(K,n)-1}v^{k+1}
--   $$
-- source:
--   Life Contingencies §3.3.4, equations (3.19)-(3.20), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib

namespace ActuarialValuation

noncomputable def guaranteedAnnuityImmediatePV {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (max (K ω) n), v ^ (k + 1)

end ActuarialValuation



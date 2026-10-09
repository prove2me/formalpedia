-- Prove2me | Definitions.Def_actuarial_guaranteedAnnuityDuePV
-- name    : actuarial_guaranteedAnnuityDuePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T21:29:52.787072+00:00
-- url     : https://prove2.me/theorems/d90d043b-0c81-4460-a8c9-1a858fb862b5
-- title:
--   Guaranteed annuity due pv
-- statement:
--   Defines a due annuity whose payments are certain from time zero through the guaranteed term, then continue while the lifetime condition holds. A zero term gives the whole-life annuity due.
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{guaranteed,due}}=\sum_{k=0}^{\max(K+1,n)-1}v^k
--   $$
-- source:
--   Life Contingencies §3.3.4, equations (3.19)-(3.20), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib

namespace ActuarialValuation

noncomputable def guaranteedAnnuityDuePV {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (max (K ω + 1) n), v ^ k

end ActuarialValuation



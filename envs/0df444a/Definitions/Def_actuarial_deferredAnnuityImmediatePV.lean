-- Prove2me | Definitions.Def_actuarial_deferredAnnuityImmediatePV
-- name    : actuarial_deferredAnnuityImmediatePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T20:34:59.04619+00:00
-- url     : https://prove2.me/theorems/430e42b5-f878-441c-a9d7-6bbf9f64d625
-- title:
--   Deferred whole-life annuity payable in arrears
-- statement:
--   After deferral for n years, the first potential arrears payment is at time n plus one, and payments continue through K. When n is zero this is the whole-life annuity in arrears; when K equals n there is no payment at time n plus one.
--
--   $$
--   Z_{\mathrm{deferred,immediate}}=\sum_{k=n}^{K-1}v^{k+1}\ \mathbf1_{\{K\ge n+1\}}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.3 eqs (3.17)–(3.18), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib

namespace ActuarialValuation

noncomputable def deferredAnnuityImmediatePV {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (K ω), if n ≤ k then v ^ (k + 1) else 0

end ActuarialValuation



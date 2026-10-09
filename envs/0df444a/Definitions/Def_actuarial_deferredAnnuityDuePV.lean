-- Prove2me | Definitions.Def_actuarial_deferredAnnuityDuePV
-- name    : actuarial_deferredAnnuityDuePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T20:34:17.916332+00:00
-- url     : https://prove2.me/theorems/5e539263-0c2c-4d8e-8386-a99c8af36057
-- title:
--   Deferred whole-life annuity payable in advance
-- statement:
--   After deferral for n years, payments are due at times n through K, provided K is at least n. When n is zero this is the whole-life annuity in advance; when K equals n, the payment at time n is included.
--
--   $$
--   Z_{\mathrm{deferred,due}}=\sum_{k=n}^{K}v^k\ \mathbf1_{\{K\ge n\}}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.3 eqs (3.17)–(3.18), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib

namespace ActuarialValuation

noncomputable def deferredAnnuityDuePV {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (K ω + 1), if n ≤ k then v ^ k else 0

end ActuarialValuation



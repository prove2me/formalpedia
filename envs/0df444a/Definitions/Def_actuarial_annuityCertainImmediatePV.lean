-- Prove2me | Definitions.Def_actuarial_annuityCertainImmediatePV
-- name    : actuarial_annuityCertainImmediatePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T21:29:36.506733+00:00
-- url     : https://prove2.me/theorems/f56d028a-1062-474b-ba9b-f8866de9de2d
-- title:
--   Annuity certain immediate pv
-- statement:
--   Defines the present value of a certain immediate annuity, with payments at times one through the stated term.
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{certain,immediate}}=\sum_{k=0}^{n-1}v^{k+1}
--   $$
-- source:
--   Life Contingencies §3.3.4, equations (3.19)-(3.20), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib

namespace ActuarialValuation

noncomputable def annuityCertainImmediatePV (v : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, v ^ (k + 1)

end ActuarialValuation



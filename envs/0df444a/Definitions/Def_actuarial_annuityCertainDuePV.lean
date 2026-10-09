-- Prove2me | Definitions.Def_actuarial_annuityCertainDuePV
-- name    : actuarial_annuityCertainDuePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T21:28:52.087123+00:00
-- url     : https://prove2.me/theorems/faaebf8a-58f2-4c73-9613-cbefe91308df
-- title:
--   Annuity certain due pv
-- statement:
--   Defines the present value of a certain annuity due, with payments at times zero through one period before the stated term.
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{certain,due}}=\sum_{k=0}^{n-1}v^k
--   $$
-- source:
--   Life Contingencies §3.3.4, equations (3.19)-(3.20), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib

namespace ActuarialValuation

noncomputable def annuityCertainDuePV (v : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, v ^ k

end ActuarialValuation



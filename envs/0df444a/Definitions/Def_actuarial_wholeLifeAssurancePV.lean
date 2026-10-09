-- Prove2me | Definitions.Def_actuarial_wholeLifeAssurancePV
-- name    : actuarial_wholeLifeAssurancePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T21:36:27.608773+00:00
-- url     : https://prove2.me/theorems/d0ff5627-33aa-4923-bfff-50c952d4b5b7
-- title:
--   Whole-life assurance present value
-- statement:
--   Defines the present value of a unit whole-life assurance paid at the end of the year of death, as v^(K+1) for lifetime K and discount factor v.
--
--   **Mathematical statement**
--
--   $$
--   Z_A=v^{K+1}
--   $$
-- source:
--   Life Contingencies Chapter 3 §3.2.1 equation (3.7), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib

namespace ActuarialValuation

noncomputable def wholeLifeAssurancePV {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (ω : Ω) : ℝ :=
  v ^ (K ω + 1)

end ActuarialValuation



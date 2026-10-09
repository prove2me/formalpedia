-- Prove2me | Definitions.Def_actuarial_pureEndowmentPV
-- name    : actuarial_pureEndowmentPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T19:11:56.26672+00:00
-- url     : https://prove2.me/theorems/cd5661ef-4397-41a9-bf43-3969bb7f2b4d
-- title:
--   Exact-lifetime pure endowment present value
-- statement:
--   This present value is a unit payment at maturity if the exact lifetime is strictly greater than the term, and zero otherwise. Death exactly at maturity does not trigger it.
--
--   $$
--   Z_{\mathrm{pure}}=v^n\mathbf1_{\{T>n\}}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.2.3, equation (3.9), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_strictSurvivalEvent

namespace ActuarialValuation

noncomputable def pureEndowmentPV {Ω : Type*}
    (T : Ω → ℝ) (v : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  v ^ n * (strictSurvivalEvent T n).indicator (fun _ : Ω => (1 : ℝ)) ω

end ActuarialValuation



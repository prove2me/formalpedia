-- Prove2me | Definitions.Def_actuarial_termAssurancePV
-- name    : actuarial_termAssurancePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T17:41:28.195667+00:00
-- url     : https://prove2.me/theorems/d51afc0b-eb07-4e60-82ed-16139e9a2e6e
-- title:
--   Finite n-year level term-assurance present value
-- statement:
--   A unit term-assurance policy pays at the end of policy year k+1 if death occurs in that year, for k from zero to n−1. This is the finite-term instance of the generic presentValue from Actuarial Mathematics I.
--
--   $$
--   Z_n(\omega)=\sum_{k=0}^{n-1}v^{k+1}\mathbf1_{\{K=k\}}(\omega)
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.2.2, equation (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_presentValue
import Definitions.Def_actuarial_deathYearEvent

namespace ActuarialValuation

noncomputable def termAssurancePV {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  presentValue (Finset.range n) (fun k : ℕ => k + 1)
    (fun t : ℕ => v ^ t) (fun _ : ℕ => (1 : ℝ))
    (deathYearEvent K) ω

end ActuarialValuation



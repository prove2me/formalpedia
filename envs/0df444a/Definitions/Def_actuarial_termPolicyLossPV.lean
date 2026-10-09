-- Prove2me | Definitions.Def_actuarial_termPolicyLossPV
-- name    : actuarial_termPolicyLossPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T22:26:36.135987+00:00
-- url     : https://prove2.me/theorems/728812a1-cf70-43ad-a8ad-326f74558b5a
-- title:
--   Realised loss at issue for a level-premium term policy
-- statement:
--   Defines insurer's realised discounted loss as benefit outgo less premium income.
--
--   **Mathematical statement**
--
--   $$
--   L_n(\omega;\pi,b)=bA_n(\omega)-\pi Y_n(\omega)
--   $$
-- source:
--   Dickson, Hardy and Waters (2009 first edition), Actuarial Mathematics for Life Contingent Risks, Chapter 6 §6.4 (net future-loss PV) and §6.5.1, equation (6.1) (net equivalence principle), equation (6.2) (worked endowment net premium); https://doi.org/10.1017/CBO9780511800146; finite n-year assurance from Life Contingencies Ch. 3 §3.2.2 (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_premiumDuePV
open MeasureTheory

namespace ActuarialValuation

noncomputable def termPolicyLossPV {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (n : ℕ)
    (b π : ℝ) (ω : Ω) : ℝ :=
  b * termAssurancePV K v n ω - π * premiumDuePV K v n ω

end ActuarialValuation



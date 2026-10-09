-- Prove2me | Definitions.Def_actuarial_netLevelPremium
-- name    : actuarial_netLevelPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T22:28:02.615073+00:00
-- url     : https://prove2.me/theorems/f531efb5-3ba3-4ce2-87d6-ce3e46e44aca
-- title:
--   Equivalence-principle net level premium
-- statement:
--   Defines net premium as the ratio of expected claim PV to expected premium annuity PV, with the positive-denominator obligation kept explicit in subsequent theorems.
--
--   **Mathematical statement**
--
--   $$
--   \pi^*=\frac{b\,\mathbb E_P[A_n]}{\mathbb E_P[Y_n]}
--   $$
-- source:
--   Dickson, Hardy and Waters (2009 first edition), Actuarial Mathematics for Life Contingent Risks, Chapter 6 §6.4 (net future-loss PV) and §6.5.1, equation (6.1) (net equivalence principle), equation (6.2) (worked endowment net premium); https://doi.org/10.1017/CBO9780511800146; finite n-year assurance from Life Contingencies Ch. 3 §3.2.2 (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_premiumDuePV
open MeasureTheory

namespace ActuarialValuation

noncomputable def netLevelPremium {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (K : Ω → ℕ) (v : ℝ) (n : ℕ) (b : ℝ) : ℝ :=
  b * (∫ ω, termAssurancePV K v n ω ∂P) /
      (∫ ω, premiumDuePV K v n ω ∂P)

end ActuarialValuation



-- Prove2me | Definitions.Def_actuarial_premiumDuePV
-- name    : actuarial_premiumDuePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T22:13:43.352804+00:00
-- url     : https://prove2.me/theorems/aae3641b-5942-43a0-bcda-787cfe6ede66
-- title:
--   Finite level-premium annuity-due present value
-- statement:
--   For a term of n years, pays one premium at time k when k<n and K≥k.
--
--   **Mathematical statement**
--
--   $$
--   Y_n(\omega)=\sum_{0\le k<n}v^k\mathbf1_{\{K(\omega)\ge k\}}
--   $$
-- source:
--   Dickson, Hardy and Waters (2009 first edition), Actuarial Mathematics for Life Contingent Risks, Chapter 6 §6.4 (net future-loss PV) and §6.5.1, equation (6.1) (net equivalence principle), equation (6.2) (worked endowment net premium); https://doi.org/10.1017/CBO9780511800146; finite n-year assurance from Life Contingencies Ch. 3 §3.2.2 (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
open MeasureTheory

namespace ActuarialValuation

noncomputable def premiumDuePV {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, if k ≤ K ω then v ^ k else 0

end ActuarialValuation



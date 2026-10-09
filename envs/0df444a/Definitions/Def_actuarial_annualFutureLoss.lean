-- Prove2me | Definitions.Def_actuarial_annualFutureLoss
-- name    : actuarial_annualFutureLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:05:21.137717+00:00
-- url     : https://prove2.me/theorems/5ee6d5b7-ab50-411d-8044-56b081e00f80
-- title:
--   Realised net future loss before the time-t premium
-- statement:
--   The remaining death benefit less the remaining annual premiums, valued immediately before the time-t premium.
--
--   **Mathematical statement**
--
--   $$
--   L_t(\omega)=b\,v^{K+1-t}\mathbf1_{\{t\le K<n\}}-\pi\sum_{t\le j<n}v^{j-t}\mathbf1_{\{K\ge j\}}
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Ch.6 §6.3, equations (6.3.4)-(6.3.10); Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Ch.7 §7.3.3, https://doi.org/10.1017/CBO9780511800146.008

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def annualFutureLoss {Ω : Type*}
  (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (b π : ℝ) (ω : Ω) : ℝ :=
  (if t ≤ K ω ∧ K ω < n then b * v ^ (K ω + 1 - t) else 0) -
  π * (∑ j ∈ Finset.range n,
    if t ≤ j ∧ j ≤ K ω then v ^ (j - t) else 0)

end ActuarialValuation



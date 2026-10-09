-- Prove2me | Definitions.Def_actuarial_discountedAnnualGainSum
-- name    : actuarial_discountedAnnualGainSum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:16:20.16736+00:00
-- url     : https://prove2.me/theorems/76d1b466-e03f-4ddc-bcdf-fddb8e36e51d
-- title:
--   Total discounted finite series of annual gains
-- statement:
--   Aggregates n annual insurer gains back to issue using v to the year index.
--
--   **Mathematical statement**
--
--   $$
--   L_n=\sum_{0\le k<n}v^kG_k
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def discountedAnnualGainSum {Ω : Type*}
  (G : ℕ → Ω → ℝ) (v : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, v ^ k * G k ω

end ActuarialValuation



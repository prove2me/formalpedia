-- Prove2me | Definitions.Def_actuarial_wholeLifeYearInnovation
-- name    : actuarial_wholeLifeYearInnovation
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T09:59:35.638426+00:00
-- url     : https://prove2.me/theorems/b35d7cd0-85b1-4b8d-86b6-02c6c5f790fc
-- title:
--   Centred one-year mortality innovation
-- statement:
--   This is an observed death-in-year indicator minus the year-t conditional death probability times the in-force indicator. The denominator is the unbounded-lifetime survival mass, so the downstream probabilistic statements explicitly require that denominator to be strictly positive.
--
--   **Mathematical statement**
--
--   $$
--   I_t(k)=\mathbf1_{\{k=t\}}-(w_t/S_t)\mathbf1_{\{k\ge t\}}
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, DOI https://doi.org/10.1007/s13385-020-00256-9; original countable-L2 extension in this mission

import Mathlib
import Definitions.Def_actuarial_wholeLifeTailMass

namespace ActuarialValuation

noncomputable def wholeLifeYearInnovation (w : ℕ → ℝ) (t k : ℕ) : ℝ :=
  (if k = t then 1 else 0) -
    (w t / wholeLifeTailMass w t) * (if t ≤ k then 1 else 0)

end ActuarialValuation



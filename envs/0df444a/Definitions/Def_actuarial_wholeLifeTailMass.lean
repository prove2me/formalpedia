-- Prove2me | Definitions.Def_actuarial_wholeLifeTailMass
-- name    : actuarial_wholeLifeTailMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T09:58:54.231004+00:00
-- url     : https://prove2.me/theorems/c66e4d34-7d69-42e2-96a4-76082b5c7eda
-- title:
--   Unbounded curtate-lifetime survival mass
-- statement:
--   At policy year t an insured is in force exactly if the realised curtate death year k is at least t. The survival mass is a countable tail sum of death-year weights. Normalisation and positivity are imposed when interpreting this algebra as a genuine mortality model.
--
--   **Mathematical statement**
--
--   $$
--   S_t=\sum_{k\ge t}w_k
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, DOI https://doi.org/10.1007/s13385-020-00256-9; original countable-L2 extension in this mission

import Mathlib

namespace ActuarialValuation

noncomputable def wholeLifeTailMass (w : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑' k : ℕ, if t ≤ k then w k else 0

end ActuarialValuation



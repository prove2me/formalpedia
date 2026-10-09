-- Prove2me | Definitions.Def_actuarial_decrementSavingsPremium
-- name    : actuarial_decrementSavingsPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:19:43.914982+00:00
-- url     : https://prove2.me/theorems/42d2e5b9-c6e7-4076-9d30-eb2934842d4c
-- title:
--   Savings component of annual reserve premium
-- statement:
--   Part of the premium needed to move from opening reserve to the one-year discounted following reserve.
--
--   **Mathematical statement**
--
--   $$
--   \Pi^{\rm sav}=vR_+-R
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Chapter 7 §7.5, equations (7.5.1)-(7.5.5); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §8.8 multiple decrement models, https://doi.org/10.1017/CBO9780511800146.009

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def decrementSavingsPremium
  (v R Rnext : ℝ) : ℝ := v * Rnext - R

end ActuarialValuation



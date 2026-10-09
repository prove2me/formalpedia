-- Prove2me | Definitions.Def_actuarial_decrementRiskPremium
-- name    : actuarial_decrementRiskPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:19:56.160987+00:00
-- url     : https://prove2.me/theorems/27905e1a-4f50-4592-9c9c-6d4bad2189d0
-- title:
--   Cause-specific risk premium over next-year reserve
-- statement:
--   One-year premium for cause-dependent net amounts at risk b_j less the next-year reserve.
--
--   **Mathematical statement**
--
--   $$
--   \Pi^{\rm risk}=v\sum_jq_j(b_j-R_+)
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Chapter 7 §7.5, equations (7.5.1)-(7.5.5); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §8.8 multiple decrement models, https://doi.org/10.1017/CBO9780511800146.009

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def decrementRiskPremium {J : Type*} [Fintype J]
  (q b : J → ℝ) (v Rnext : ℝ) : ℝ :=
  v * ∑ j : J, q j * (b j - Rnext)

end ActuarialValuation



-- Prove2me | Definitions.Def_actuarial_cm1ServiceOneYearSurvival
-- name    : actuarial_cm1ServiceOneYearSurvival
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T22:45:06.565987+00:00
-- url     : https://prove2.me/theorems/8dc1c91f-940a-47f8-9590-c4437bb25180
-- title:
--   Cause probabilities and transitions: cm1ServiceOneYearSurvival
-- statement:
--   Conditional probability of staying active for one additional year. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   p_t=l_{t+1}/l_t
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Multiple State Models, Chapter 8, printed page 256, multiple decrement models; Chapter 9, page 297, pension service tables. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapters 8-9, multiple decrement models and pension service tables, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: Pension service tables, retirement withdrawal and death as competing decrement causes, conservation of cohort mass and actuarial benefit PV. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cm1ServiceOneYearSurvival (l : ℕ → ℝ) (t : ℕ) : ℝ := l (t+1) / l t

end ActuarialValuation



-- Prove2me | Definitions.Def_actuarial_annualProspectiveReserve
-- name    : actuarial_annualProspectiveReserve
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:10:15.933886+00:00
-- url     : https://prove2.me/theorems/f7a875d9-958b-472c-bc0e-9a8d01c808f5
-- title:
--   Conditional annual net premium reserve
-- statement:
--   Expected remaining insurer loss per surviving policy. Theorems assume positive survival probability when interpreting this as a conditional reserve.
--
--   **Mathematical statement**
--
--   $$
--   V_t=\mathbb E[L_t]/S_t,\quad S_t>0
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Ch.6 §6.3, equations (6.3.4)-(6.3.10); Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Ch.7 §7.3.3, https://doi.org/10.1017/CBO9780511800146.008

import Mathlib
import Definitions.Def_actuarial_annualFutureLoss
import Definitions.Def_actuarial_annualSurvivalMass
open MeasureTheory

namespace ActuarialValuation

noncomputable def annualProspectiveReserve {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (b π : ℝ) : ℝ :=
  (∫ ω, annualFutureLoss K v n t b π ω ∂P) /
    annualSurvivalMass P K t

end ActuarialValuation



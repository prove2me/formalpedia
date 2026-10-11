-- Prove2me | Definitions.Def_actuarial_irClaimCostUltimate
-- name    : actuarial_irClaimCostUltimate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:00:07.507913+00:00
-- url     : https://prove2.me/theorems/7fc168d9-411a-452e-a711-21edf4e499ae
-- title:
--   Average-cost-per-claim projection and reserve reconciliation: irClaimCostUltimate
-- statement:
--   Independent average-cost-triangle projection of ultimate severity per claim. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   U_i=N_i^{\text{ult}}A_i^{\text{ult}},\quad R_i=U_i-P_i
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 382. Institute and Faculty of Actuaries, High-level Methods for Incorporating Changing Inflation into Claims Reserve Estimates, https://vle.actuaries.org.uk/pluginfile.php/168696/mod_resource/content/1/Reserving%20During%20Volatile%20Inflation%20v1.9.pdf; IFoA Claims Reserving report, https://www.actuaries.org.uk/system/files/documents/pdf/0353-0413.pdf. Parent topic: Inflation-adjusted incremental triangle with calendar-year indices, de-inflation, development and reinflation; claim-frequency and average-cost ultimate reserve reconciliation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0353-0413.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def irClaimCostUltimate (observedAvg costFactor : ℝ) : ℝ := observedAvg*costFactor

end ActuarialValuation



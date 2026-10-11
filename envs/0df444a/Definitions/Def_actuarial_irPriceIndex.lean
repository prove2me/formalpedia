-- Prove2me | Definitions.Def_actuarial_irPriceIndex
-- name    : actuarial_irPriceIndex
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T18:58:43.360707+00:00
-- url     : https://prove2.me/theorems/db853f4c-219e-4154-a470-0df52958c6a2
-- title:
--   Inflation indices and real-claims transformations: irPriceIndex
-- statement:
--   Calendar-year claim cost index after a real actuarial claims inflation assumption. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   C^{\text{real}}_{i,j}=C_{i,j}\frac{I_{\text{base}}}{I_{i+j}}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 382. Institute and Faculty of Actuaries, High-level Methods for Incorporating Changing Inflation into Claims Reserve Estimates, https://vle.actuaries.org.uk/pluginfile.php/168696/mod_resource/content/1/Reserving%20During%20Volatile%20Inflation%20v1.9.pdf; IFoA Claims Reserving report, https://www.actuaries.org.uk/system/files/documents/pdf/0353-0413.pdf. Parent topic: Inflation-adjusted incremental triangle with calendar-year indices, de-inflation, development and reinflation; claim-frequency and average-cost ultimate reserve reconciliation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0353-0413.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def irPriceIndex (baseIndex growth : ℝ) : ℝ := baseIndex*(1+growth)

end ActuarialValuation



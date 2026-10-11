-- Prove2me | Definitions.Def_actuarial_irIncrement
-- name    : actuarial_irIncrement
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T18:59:08.657877+00:00
-- url     : https://prove2.me/theorems/f4421f99-8ce0-440c-8346-dba4f6d3b629
-- title:
--   Incremental triangles and cumulative development: irIncrement
-- statement:
--   Increments from an accident-year cumulative claims development row. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   C_{i,j}=\sum_{k=0}^{j}X_{i,k},\quad U_i=C_{i,j}f_j
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 382. Institute and Faculty of Actuaries, High-level Methods for Incorporating Changing Inflation into Claims Reserve Estimates, https://vle.actuaries.org.uk/pluginfile.php/168696/mod_resource/content/1/Reserving%20During%20Volatile%20Inflation%20v1.9.pdf; IFoA Claims Reserving report, https://www.actuaries.org.uk/system/files/documents/pdf/0353-0413.pdf. Parent topic: Inflation-adjusted incremental triangle with calendar-year indices, de-inflation, development and reinflation; claim-frequency and average-cost ultimate reserve reconciliation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0353-0413.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def irIncrement (cumulative : ℕ → ℝ) (j : ℕ) : ℝ := cumulative (j+1)-cumulative j

end ActuarialValuation



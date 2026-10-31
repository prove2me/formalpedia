-- Prove2me | Definitions.Def_RepairSched_Model_expBackorder
-- name    : RepairSched_Model_expBackorder
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:47.027829+00:00
-- url     : https://prove2.me/theorems/dec5e365-7d38-484a-9d4b-7280ea0abe74
-- title:
--   Expected cumulative backorder cost
-- statement:
--   This is the expected backorder cost up to time $t$,
--   $$\mathbf E\Big[\sum_i b_i\int_0^t(a_i(s)-S_i)^+\,ds\Big]\in[0,\infty].$$
--
--   **Formalization Note** All integrands are nonnegative, so an infinite expectation is $\infty$, never a junk value.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), (10a), p.17

import Mathlib
import Definitions.Def_RepairSched_Model

open MeasureTheory Set

namespace RepairSched

/-- **The expected cumulative backorder cost**
`E[Σᵢ bᵢ ∫₀ᵗ (aᵢ(s,W(s)) − Sᵢ)⁺ ds]`, in `ℝ≥0∞`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), (10a), p.17.

**Formalization Note.** All integrands are nonnegative, so an infinite expectation is `∞`, never
a junk value. -/
noncomputable def Model.expBackorder {n : ℕ} (M : Model n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S : Fin n → ℝ) (a : ℝ → Ω → Fin n → ℝ) (t : ℝ) : ENNReal :=
  ∫⁻ ω, ∑ i, ENNReal.ofReal (M.b i) * (∫⁻ s in Icc 0 t, ENNReal.ofReal (max (a s ω i - S i) 0)) ∂P

end RepairSched



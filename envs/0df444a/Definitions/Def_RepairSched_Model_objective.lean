-- Prove2me | Definitions.Def_RepairSched_Model_objective
-- name    : RepairSched_Model_objective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:43.308828+00:00
-- url     : https://prove2.me/theorems/6547c436-e1a3-4e34-b595-0dc0cebb4731
-- title:
--   The objective (10a) of the EWF
-- statement:
--   The objective of the EWF is
--   $$\limsup_{t\to\infty}\ \sum_ih_iS_i+\frac1t\,\mathbf E\Big[\sum_ib_i\int_0^t(a_i(s)-S_i)^+\,ds+c_k\mu_kE(t)\Big]\in[0,\infty].$$
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), (10a), p.17

import Mathlib
import Definitions.Def_RepairSched_Model
import Definitions.Def_RepairSched_Model_avgBOE

open MeasureTheory Filter

namespace RepairSched

/-- **The objective (10a) of the EWF**:
`limsup_{t→∞} E[Σᵢ hᵢSᵢ + (1/t)(Σᵢ bᵢ ∫₀ᵗ (aᵢ(s,W(s)) − Sᵢ)⁺ ds + ckμkE(t))]`, in `ℝ≥0∞`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), (10a), p.17. -/
noncomputable def Model.objective {n : ℕ} [NeZero n] (M : Model n) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (S : Fin n → ℝ) (E : ℝ → Ω → ℝ)
    (a : ℝ → Ω → Fin n → ℝ) : ENNReal :=
  limsup (fun t : ℝ => ∑ i, ENNReal.ofReal (M.h i * S i) + M.avgBOE P S E a t) atTop

end RepairSched



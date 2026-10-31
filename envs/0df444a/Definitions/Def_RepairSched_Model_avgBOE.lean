-- Prove2me | Definitions.Def_RepairSched_Model_avgBOE
-- name    : RepairSched_Model_avgBOE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:47.943355+00:00
-- url     : https://prove2.me/theorems/576a754c-08b9-4370-9d5e-5994f314b307
-- title:
--   Average backorder and emergency repair cost up to $t$
-- statement:
--   This is the average cost up to time $t$,
--   $$\frac1t\,\mathbf E\Big[\sum_i b_i\int_0^t(a_i(s)-S_i)^+\,ds+c_k\mu_kE(t)\Big]\in[0,\infty].$$
--
--   **Formalization Note** It is used only along $t\to\infty$.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), (10a), p.17; (A.58), OA p.35

import Mathlib
import Definitions.Def_RepairSched_Model
import Definitions.Def_RepairSched_Model_emergencyRate
import Definitions.Def_RepairSched_Model_expBackorder

open MeasureTheory

namespace RepairSched

/-- **The average backorder and emergency repair cost up to time `t`**,
`(1/t) E[Σᵢ bᵢ ∫₀ᵗ (aᵢ(s,W(s)) − Sᵢ)⁺ ds + ckμkE(t)]`, in `ℝ≥0∞`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), (10a), p.17, and (A.58), OA p.35.

**Formalization Note.** The expectation of the sum is written as the sum of the two expectations.
Division by `ofReal t` is only meaningful for `t > 0`; the quantity is used only along
`t → ∞`. -/
noncomputable def Model.avgBOE {n : ℕ} [NeZero n] (M : Model n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S : Fin n → ℝ) (E : ℝ → Ω → ℝ) (a : ℝ → Ω → Fin n → ℝ) (t : ℝ) : ENNReal :=
  (M.expBackorder P S a t + ENNReal.ofReal M.emergencyRate * ∫⁻ ω, ENNReal.ofReal (E t ω) ∂P) /
    ENNReal.ofReal t

end RepairSched



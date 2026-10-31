-- Prove2me | Definitions.Def_RepairSched_Model_IsBarrierPolicy
-- name    : RepairSched_Model_IsBarrierPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:53:13.633374+00:00
-- url     : https://prove2.me/theorems/2688b791-384d-468f-aa72-dc00b210c369
-- title:
--   The barrier policy with barriers $0$ and $B$
-- statement:
--   The barrier policy is a feasible $(W,I,E,a,S)$ which, for almost every $\omega$, satisfies C1–C3 for the drift of $q^*$, the barrier $B$ and the input $X+\theta e$, with $a(t)=q^*(W(t))$.
--
--   **Formalization Note** Definition 6 reads for every $\omega$. Pathwise existence for every path is false (see Lemma 4), so the barrier property holds almost surely, while the constraints (10b)–(10f) hold for every $\omega$.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Definition 6, p.25

import Mathlib
import Definitions.Def_RepairSched_Model
import Definitions.Def_RepairSched_Model_IsFeasible
import Definitions.Def_RepairSched_Model_IsBarrierPath
import Definitions.Def_RepairSched_Model_qStar

open MeasureTheory

namespace RepairSched

/-- **The barrier policy** with lower barrier `0` and upper barrier `B`: an EWF-feasible
`(W, I, E, a, S)` that, for `P`-almost every `ω`, is the regulator output of Definition 6 with
`a(t) = q*(W(t))` for `t ≥ 0`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Definition 6, p.25.

**Formalization Note.** Definition 6 reads for every `ω`. Pathwise existence for every `ω` can fail
because the printed Lemma 4 is false for some continuous paths (see `lemma_4`), so the barrier
property holds almost surely; the EWF constraints (10b)–(10f) still hold for every `ω`. -/
def Model.IsBarrierPolicy {n : ℕ} [NeZero n] (M : Model n) {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (𝔽 : Filtration ℝ mΩ) (P : Measure Ω) (S : Fin n → ℝ) (f : ℝ → ℝ)
    (B : ℝ) (X W I E : ℝ → Ω → ℝ) (a : ℝ → Ω → Fin n → ℝ) : Prop :=
  M.IsFeasible 𝔽 X S W I E a ∧
    ∀ᵐ ω ∂P, M.IsBarrierPath S f B X W I E ω ∧
      ∀ t, 0 ≤ t → a t ω = M.qStar S (deriv f (W t ω)) (W t ω)

end RepairSched



-- Prove2me | Definitions.Def_RepairSched_UsualConditions
-- name    : RepairSched_UsualConditions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:45:07.325986+00:00
-- url     : https://prove2.me/theorems/e19cd62d-11d1-4d70-801a-7966ed1d4fde
-- title:
--   The usual conditions
-- statement:
--   A filtered probability space satisfies the usual conditions if the filtration is right-continuous and its time-zero $\sigma$-algebra contains every $P$-null set.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), p.16

import Mathlib

open MeasureTheory

namespace RepairSched

/-- **The usual conditions** for the filtered probability space `(Ω, F, 𝔽, P)`: `𝔽` is
right-continuous and `𝔽 0` contains every `P`-null set.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), p.16: "the filtered probability space (Ω,F,F,P) satisfying the usual conditions".

**Formalization Note.** `P N` for an arbitrary set `N` is the outer measure, so `P N = 0`
covers subsets of measurable null sets. -/
def UsualConditions {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝔽 : Filtration ℝ mΩ) (P : Measure Ω) :
    Prop :=
  𝔽.IsRightContinuous ∧ ∀ N : Set Ω, P N = 0 → MeasurableSet[𝔽 0] N

end RepairSched



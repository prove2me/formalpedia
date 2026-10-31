-- Prove2me | Definitions.Def_RepairSched_IsCadlag
-- name    : RepairSched_IsCadlag
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:45:08.997988+00:00
-- url     : https://prove2.me/theorems/ce9b53d6-8adb-4435-8b15-a090969dc060
-- title:
--   The càdlàg space $\mathbb D$ on $[0,\infty)$
-- statement:
--   A function is in $\mathbb D$ if it is right-continuous at every $t\ge0$ and has a finite left limit at every $t>0$.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), p.14

import Mathlib

open Set Filter Topology

namespace RepairSched

/-- **Membership in the càdlàg space `D`** on `[0,∞)`: right-continuous at every `t ≥ 0` with a
finite left limit at every `t > 0`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), p.14: "Let D denote the càdlàg space". -/
def IsCadlag (g : ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ t → ContinuousWithinAt g (Ici t) t) ∧
    ∀ t, 0 < t → ∃ L, Tendsto g (𝓝[<] t) (𝓝 L)

end RepairSched



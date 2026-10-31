-- Prove2me | Definitions.Def_RepairSched_Model_IsBarrierPath
-- name    : RepairSched_Model_IsBarrierPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:33.779125+00:00
-- url     : https://prove2.me/theorems/befcf833-20cb-4f0f-8020-821fa114b963
-- title:
--   The barrier policy along one sample path
-- statement:
--   Along the sample path $\omega$, the triple $(W,I,E)$ satisfies C1–C3 for the drift of $q^*$, the barrier $B$ and the input $X+\theta e$, where $e(t)=t$.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Definition 6, p.25

import Mathlib
import Definitions.Def_RepairSched_Model
import Definitions.Def_RepairSched_Model_backorderRate
import Definitions.Def_RepairSched_IsRegulated

namespace RepairSched

/-- **The barrier policy along the sample path `ω`**: `(W, I, E)` at `ω` is the output of the
two-sided regulator of Definition 5 for the input `X + θe` with barrier `B`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Definition 6, p.25: `(W,I,E) = (φ⁽²⁾,ψ₁⁽²⁾,ψ₂⁽²⁾)(λ,μ,S,B,X + θe)`, where `e(t) = t` (p.14). -/
def Model.IsBarrierPath {n : ℕ} [NeZero n] (M : Model n) {Ω : Type*} (S : Fin n → ℝ)
    (f : ℝ → ℝ) (B : ℝ) (X W I E : ℝ → Ω → ℝ) (ω : Ω) : Prop :=
  IsRegulated (M.backorderRate S f) B (fun t => X t ω + M.theta * t) (fun t => W t ω)
    (fun t => I t ω) (fun t => E t ω)

end RepairSched



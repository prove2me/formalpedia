-- Prove2me | Definitions.Def_VehShare_SeqBounds_Slot
-- name    : VehShare_SeqBounds_Slot
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:34:35.421592+00:00
-- url     : https://prove2.me/theorems/af8ad519-64a5-4c5c-9347-7b61bf495dae
-- title:
--   Slots of the closed queueing network
-- statement:
--   A **slot** is a place a vehicle can occupy: a location $i$ (its pick-up queue) or a stage $s$ of the transit queue of a pair $(i,j)$. Footnote 1 (p. 4): "The state of the system can be specified in terms of the current number of vehicles at each location and at each stage of the transit queue from each location to any other location."
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, footnote 1, p. 4

import Mathlib
import Definitions.Def_VehShare_SeqBounds_Instance

namespace VehShare.SeqBounds

/-- **Slots a vehicle can occupy.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), footnote 1, p. 4: "The state of the system can be specified in terms of the current number of
vehicles at each location and at each stage of the transit queue from each location to any other
location."

A slot is a location `Sum.inl i` (the pick-up queue of `i`) or a stage `Sum.inr ⟨(i, j), s⟩` of the
transit queue of the pair `(i, j)`. -/
abbrev Slot (P : Instance) : Type := P.L ⊕ (Σ p : P.L × P.L, P.Ph p.1 p.2)

end VehShare.SeqBounds



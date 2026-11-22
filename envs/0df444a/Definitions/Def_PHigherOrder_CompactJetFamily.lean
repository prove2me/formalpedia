-- Prove2me | Definitions.Def_PHigherOrder_CompactJetFamily
-- name    : PHigherOrder_CompactJetFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:16:07.158699+00:00
-- url     : https://prove2.me/theorems/95f75a7e-92bc-4f29-998f-15ff3aac7d1c
-- title:
--   Compact Jet Family
-- statement:
--   Definitions and structural lemmas for Compact Jet Family, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/CompactJetFamily.lean

import Definitions.Def_PHigherOrder_XHalf
import Definitions.Def_PHigherOrder_IsPHarm
set_option autoImplicit false
noncomputable def CompactJetFamily (p : ℝ) : Set (BoundedContinuousFunction XHalf (ℝ × Plane)) :=
  closure {z : BoundedContinuousFunction XHalf (ℝ × Plane) | ∃ (v : Plane → ℝ) (g : Plane → Plane),
    IsPHarm p (Metric.ball 0 1) v g ∧
    (∀ x ∈ Metric.ball (0 : Plane) 1, |v x| ≤ 1) ∧
    v 0 = 0 ∧
    ∀ x : XHalf, z x = (v (x : Plane), gradient v (x : Plane))}



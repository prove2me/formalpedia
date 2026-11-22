-- Prove2me | Definitions.Def_PHigherOrder_LewisRigidityInput
-- name    : PHigherOrder_LewisRigidityInput
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:14:47.139332+00:00
-- url     : https://prove2.me/theorems/eaabb51c-e68b-4da1-9086-65f04d86a2e9
-- title:
--   Lewis Rigidity Input
-- statement:
--   Definitions and structural lemmas for Lewis Rigidity Input, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/LewisRigidityInput.lean

import Definitions.Def_PHigherOrder_IsPHarm
set_option autoImplicit false
structure LewisRigidityInput (p : ℝ) : Prop where
  vanish : ∀ m : ℕ, 2 ≤ m →
      ∀ (Q : ContinuousMultilinearMap ℝ (fun _ : Fin m => Plane) ℝ) (G : Plane → Plane),
        IsPHarm p Set.univ (fun x => Q fun _ => x) G →
        ∀ x : Plane, Q (fun _ => x) = 0



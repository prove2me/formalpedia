-- Prove2me | Definitions.Def_PHigherOrder_TaylorPoly
-- name    : PHigherOrder_TaylorPoly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:09:12.971447+00:00
-- url     : https://prove2.me/theorems/03cc601f-107f-46ce-bcb1-ad5560ceb789
-- title:
--   Taylor Poly
-- statement:
--   Definitions and structural lemmas for Taylor Poly, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/TaylorPoly.lean

import Definitions.Def_PHigherOrder_Plane
set_option autoImplicit false
noncomputable def TaylorPoly (k : ℕ) (u : Plane → ℝ) (x₀ : Plane) : Plane → ℝ :=
  fun z => ∑ j ∈ Finset.range (k + 1),
    (1 / (Nat.factorial j : ℝ)) * iteratedFDeriv ℝ j u x₀ (fun _ => z - x₀)



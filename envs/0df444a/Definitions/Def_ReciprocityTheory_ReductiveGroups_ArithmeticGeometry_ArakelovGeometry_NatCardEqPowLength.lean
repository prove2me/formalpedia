-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NatCardEqPowLength
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NatCardEqPowLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:35.464285+00:00
-- url     : https://prove2.me/theorems/30a90414-f04c-4db4-b42a-3392174c6c79
-- title:
--   Nat Card Eq Pow Length
-- statement:
--   Definitions and structural lemmas for Nat Card Eq Pow Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/NatCardEqPowLength.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
def dmap (W : Ideal (MRing ι)) (i : ∀ k, ι k) (a : K → ℕ) : mPiece W a → MRing ι ⧸ dehomI W i :=
  fun x => Ideal.Quotient.factor (le_sup_left : W ≤ dehomI W i) x.1
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry



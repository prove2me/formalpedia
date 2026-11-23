-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondOrderIterateEqZero
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondOrderIterateEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:13.175614+00:00
-- url     : https://prove2.me/theorems/8ca7f521-1d30-4681-82bb-b21ba9000c4a
-- title:
--   Second Order Iterate Eq Zero
-- statement:
--   Definitions and structural lemmas for Second Order Iterate Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondOrderIterateEqZero.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι]
abbrev kapE (s : ι → Bool) (κ : ι → ι → k) (i : Fin (Fintype.card {l // s l = true}))
    (j : Fin (Fintype.card {l // ¬ s l = true})) : k :=
  κ ((sideE s).symm (Sum.inl i)) ((sideE s).symm (Sum.inr j))
section Van
variable {π : Type} [Fintype π] [DecidableEq π]
end Van
end ReciprocityTheory.ChartRestriction.G.TB.SCPf



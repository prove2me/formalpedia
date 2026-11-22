-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_IsIntegralOfAll
-- name    : Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_IsIntegralOfAll
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:52.950973+00:00
-- url     : https://prove2.me/theorems/ca8c2933-aa39-4e67-9f3b-4d950625b92a
-- title:
--   Is Integral Of All
-- statement:
--   Definitions and structural lemmas for Is Integral Of All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/IsIntegralOfAll.lean

import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt
section
variable (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A]
def redAs (m : Ideal A) : ↥(As O A) →ₐ[O] ↥(As O (A ⧸ m)) :=
  ((Ideal.Quotient.mkₐ O m).comp (As O A).val).codRestrict (As O (A ⧸ m))
    fun a => (show IsIntegral O (a : A) from a.2).map (Ideal.Quotient.mkₐ O m)
end
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt



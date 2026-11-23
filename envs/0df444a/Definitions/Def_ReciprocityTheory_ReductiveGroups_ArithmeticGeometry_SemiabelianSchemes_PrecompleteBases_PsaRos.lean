-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:08.801634+00:00
-- url     : https://prove2.me/theorems/f0943775-b8d1-4a15-a7d6-e17e064960e4
-- title:
--   Psa Ros
-- statement:
--   Definitions and structural lemmas for Psa Ros, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsaRos.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AddMonoidAlgebra
namespace ReciprocityTheory.ChartRestriction.G.Semi
instance twoUniqueSums_of_free (X : Type*) [AddCommGroup X] [Module.Free ℤ X] :
    TwoUniqueSums X :=
  (AddEquiv.twoUniqueSums_iff (Module.Free.chooseBasis ℤ X).repr.toAddEquiv).mpr inferInstance
end ReciprocityTheory.ChartRestriction.G.Semi



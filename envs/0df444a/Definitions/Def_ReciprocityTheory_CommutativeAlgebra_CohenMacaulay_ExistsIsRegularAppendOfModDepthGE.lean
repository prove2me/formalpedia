-- Prove2me | Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
-- name    : ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:09.517152+00:00
-- url     : https://prove2.me/theorems/a046afe7-3d42-4717-b57b-17e361d9034a
-- title:
--   Exists Is Regular Append Of Mod Depth GE
-- statement:
--   Definitions and structural lemmas for Exists Is Regular Append Of Mod Depth GE, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactSide_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
section Noeth
variable [IsNoetherianRing R]
end Noeth
section Main
variable [IsNoetherianRing R]
end Main
variable [IsNoetherianRing R] [Module.Finite R M]
end ReciprocityTheory.CA



-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularLocalExtensionWithSimpleRoot
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularLocalExtensionWithSimpleRoot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:43.003962+00:00
-- url     : https://prove2.me/theorems/3713825e-9644-4348-9a2d-ef0b4d4c4997
-- title:
--   Exists Regular Local Extension With Simple Root
-- statement:
--   Definitions and structural lemmas for Exists Regular Local Extension With Simple Root, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularLocalExtensionWithSimpleRoot.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
namespace GlobalTheory.MonicRootExtension
section
variable {A : Type} [CommRing A] [IsLocalRing A] (M : A[X]) (hM : M.Monic)
  (hirr : Irreducible (M.map (residue A)))
include hM hirr
end
section
variable {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  (M : A[X]) (hM : M.Monic) (hirr : Irreducible (M.map (residue A)))
include hM hirr
end
end GlobalTheory.MonicRootExtension



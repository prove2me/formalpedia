-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoboundaryOfFractionCocycleHomogeneousIdea
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoboundaryOfFractionCocycleHomogeneousIdea
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:27:13.463798+00:00
-- url     : https://prove2.me/theorems/c9027041-20e4-4d1e-91c9-ccdec48809f4
-- title:
--   Exists Coboundary Of Fraction Cocycle Homogeneous Idea
-- statement:
--   Definitions and structural lemmas for Exists Coboundary Of Fraction Cocycle Homogeneous Idea, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoboundaryOfFractionCocycleHomogeneousIdea.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexGradedModuleExactAtOfLargeDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial DirectSum
namespace GlobalTheory
section GrCubeVal
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] {n : ℤ}
abbrev grCubeVal {s : Finset ι} (z : (grCube ι ℳ n).obj s) :
    LocalizedModule.Away (xProd R s) M :=
  Subtype.val (p := fun w => w ∈ homLoc ℳ s n) z
end GrCubeVal
end GlobalTheory



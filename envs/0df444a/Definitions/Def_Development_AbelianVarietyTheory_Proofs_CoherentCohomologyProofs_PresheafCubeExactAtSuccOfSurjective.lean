-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T23:19:40.339338+00:00
-- url     : https://prove2.me/theorems/0e497e28-659c-4728-a66e-aadd41e80a61
-- title:
--   Presheaf Cube Exact At Succ Of Surjective
-- statement:
--   Definitions and structural lemmas for Presheaf Cube Exact At Succ Of Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PresheafCubeExactAtSuccOfSurjective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe w v u
noncomputable section
namespace GlobalTheory
section Presheaf
variable {T : TopCat.{w}} {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
  {P : (Opens T)ᵒᵖ ⥤ ModuleCat.{w} R} (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
  (hs : ∀ ⦃W W' : Opens T⦄ (h : W' ≤ W), Function.Surjective (presheafRes P h))
include hP hs
end Presheaf
section Ab
variable {T : TopCat.{w}} {ι : Type}
def cechAbAug (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}) (V : Opens T) (U : ι → Opens T) :
    P.obj (op V) →ₗ[ℤ] Cube.Term (cechAbCube P V U) 1 :=
  presheafCechAug (P ⋙ abToIntModule) V U
variable [LinearOrder ι] [Finite ι] (F : TopCat.Sheaf AddCommGrpCat.{w} T) [F.IsFlasque]
end Ab
section Modules
variable {X : Scheme.{u}} {ι : Type} (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
  (F : X.Modules) [hF : TopCat.Presheaf.IsFlasque (X := X.toPresheafedSpace.carrier) F.presheaf]
include hF
variable [LinearOrder ι] [Finite ι]
end Modules
end GlobalTheory



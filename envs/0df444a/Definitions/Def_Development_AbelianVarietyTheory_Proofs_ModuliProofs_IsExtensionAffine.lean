-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:16:11.735596+00:00
-- url     : https://prove2.me/theorems/4549b9d8-73c5-4c79-8163-5073a746ff98
-- title:
--   Is Extension Affine
-- statement:
--   Definitions and structural lemmas for Is Extension Affine, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsExtensionAffine.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.SectionsDescent
open GlobalTheory.FieldBaseChange
def rs {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom
theorem pre_mono {X Y : Scheme.{0}} (φ : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) : φ ⁻¹ᵁ V ≤ φ ⁻¹ᵁ U :=
  fun _ hy => h hy
section Field
variable {K F : Type} [Field K] [Field F] [Algebra K F] {Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of K)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom (algebraMap K F))))
theorem pre_le_chart (M : LB Y) (p : Y' ⟶ Y) (j : PUnit → M.ι) : p ⁻¹ᵁ M.U (j PUnit.unit) ≤ (M.pull p).U j :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy
def loc {M : LB Y} (t : (M.pull p).Sec) (j : M.ι) : Γ(Y', p ⁻¹ᵁ M.U j) :=
  rs (pre_le_chart M p fun _ => j) (t.f fun _ => j)
end Field
end GlobalTheory.SectionsDescent



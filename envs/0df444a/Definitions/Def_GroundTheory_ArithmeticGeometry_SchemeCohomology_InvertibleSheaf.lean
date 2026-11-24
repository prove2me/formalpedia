-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:54.520609+00:00
-- url     : https://prove2.me/theorems/9d1ef8f7-438f-492b-a4a4-2bbc99689f2c
-- title:
--   Invertible Sheaf
-- statement:
--   Definitions and structural lemmas for Invertible Sheaf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace
universe u
namespace GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}
noncomputable instance : MonoidalCategory X.Modules :=
  sheafModulesMonoidal (Opens.grothendieckTopology X) X.sheaf
noncomputable instance : SymmetricCategory X.Modules :=
  sheafModulesSymmetric (Opens.grothendieckTopology X) X.sheaf
instance isIso_ringSheafId_scheme : IsIso (ringSheafId (Opens.grothendieckTopology X) X.sheaf) :=
  inferInstanceAs (IsIso (𝟙 (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))
variable (X) in

abbrev PMod := PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)
variable (X) in

noncomputable abbrev sheafifyMod : PMod X ⥤ X.Modules :=
  modulesSheafification (Opens.grothendieckTopology X) X.sheaf
variable (X) in

noncomputable abbrev preMod : X.Modules ⥤ PMod X :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (ringSheafId _ X.sheaf)
variable (X) in

noncomputable abbrev sheafifyModAdj : sheafifyMod X ⊣ preMod X :=
  PresheafOfModules.sheafificationAdjunction (J := Opens.grothendieckTopology X)
    (R₀ := X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) (R := X.ringCatSheaf) (ringSheafId _ X.sheaf)
instance isIso_sheafifyModAdj_counit : IsIso (sheafifyModAdj X).counit :=
  inferInstanceAs (IsIso (PresheafOfModules.sheafificationAdjunction (J := Opens.grothendieckTopology X)
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).counit)
noncomputable instance : (sheafifyMod X).Monoidal :=
  modulesSheafificationMonoidal (Opens.grothendieckTopology X) X.sheaf
noncomputable def tensorIso (M N : X.Modules) :
    (sheafifyMod X).obj ((preMod X).obj M ⊗ (preMod X).obj N) ≅ M ⊗ N :=
  (Functor.Monoidal.μIso (sheafifyMod X) _ _).symm ≪≫
    (asIso ((sheafifyModAdj X).counit.app M) ⊗ᵢ asIso ((sheafifyModAdj X).counit.app N))
noncomputable def tensorToSheaf (M N : X.Modules) :
    (preMod X).obj M ⊗ (preMod X).obj N ⟶ (preMod X).obj (M ⊗ N) :=
  (sheafifyModAdj X).unit.app _ ≫ (preMod X).map (tensorIso M N).hom
noncomputable def tensorLift {M N G : X.Modules}
    (e : (preMod X).obj M ⊗ (preMod X).obj N ⟶ (preMod X).obj G) : M ⊗ N ⟶ G :=
  (tensorIso M N).inv ≫ ((sheafifyModAdj X).homEquiv _ _).symm e
noncomputable def resM (P : PMod X) {U V : X.Opens} (h : V ≤ U) (x : P.obj (op U)) : P.obj (op V) :=
  P.map (homOfLE h).op x
abbrev ringOn (X : Scheme.{u}) (V : X.Opens) := (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)
noncomputable def resR {U V : X.Opens} (h : V ≤ U) : ringOn X U →+* ringOn X V :=
  ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map (homOfLE h).op).hom
def IsBasisOn (P : PMod X) (U : X.Opens) (s : P.obj (op U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U), Function.Bijective
    (fun r : (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op V) => r • resM P h s)
def IsInvertibleSheaf (M : X.Modules) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (s : ((preMod X).obj M).obj (op U)),
    IsBasisOn ((preMod X).obj M) U s
end GroundTheory.Arith.SchemeCoh



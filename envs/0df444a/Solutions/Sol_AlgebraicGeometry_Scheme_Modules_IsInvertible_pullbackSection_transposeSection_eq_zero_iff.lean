-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.pullbackSection_transposeSection_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/2a777f1d-6dc1-58e6-ab5b-787a25401b98

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff

section E6Coev
set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff.AlgebraicGeometry"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.IsInvertible Scheme.Modules.dual Scheme.Modules.pullbackSection Scheme.Modules.pullbackSection_def"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback mk Modules evaluation Modules.IsInvertible Modules.dual Modules.pullbackSection Modules.pullbackSection_def"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback IsInvertible dual pullbackSection pullbackSection_def IsInvertible.dual"
namespace CoevAux
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {Y : Scheme.{u}}

def tensorLeftEquivalence {Z Z' : Y.Modules} (i : Z' ⊗ Z ≅ 𝟙_ Y.Modules) (j : Z ⊗ Z' ≅ 𝟙_ Y.Modules) :
    Y.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (tensorLeft Z) (tensorLeft Z')
    ((leftUnitorNatIso Y.Modules).symm ≪≫ (tensoringLeft Y.Modules).mapIso i.symm ≪≫ tensorLeftTensor Z' Z)
    ((tensorLeftTensor Z Z').symm ≪≫ (tensoringLeft Y.Modules).mapIso j ≪≫ leftUnitorNatIso Y.Modules)

def tensorRightEquivalence {Z Z' : Y.Modules} (i : Z' ⊗ Z ≅ 𝟙_ Y.Modules) (j : Z ⊗ Z' ≅ 𝟙_ Y.Modules) :
    Y.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (tensorRight Z) (tensorRight Z')
    ((rightUnitorNatIso Y.Modules).symm ≪≫ (tensoringRight Y.Modules).mapIso j.symm ≪≫ tensorRightTensor Z Z')
    ((tensorRightTensor Z' Z).symm ≪≫ (tensoringRight Y.Modules).mapIso i ≪≫ rightUnitorNatIso Y.Modules)

theorem isEquivalence_tensorLeft {Z : Y.Modules} (hZ : Scheme.Modules.IsInvertible Z) :
    (tensorLeft Z).IsEquivalence :=
  (tensorLeftEquivalence (β_ _ _ ≪≫ hZ.dual.2.some) hZ.dual.2.some).isEquivalence_functor

theorem isEquivalence_tensorRight {Z : Y.Modules} (hZ : Scheme.Modules.IsInvertible Z) :
    (tensorRight Z).IsEquivalence :=
  (tensorRightEquivalence (β_ _ _ ≪≫ hZ.dual.2.some) hZ.dual.2.some).isEquivalence_functor

theorem isIso_ev_app (X : Y.Modules) (hX : Scheme.Modules.IsInvertible X) (N : Y.Modules) :
    IsIso ((ihom.ev X).app N) := by
  haveI := isEquivalence_tensorLeft hX
  let e : ihom X ≅ (tensorLeft X).inv :=
    (ihom.adjunction X).rightAdjointUniq (tensorLeft X).asEquivalence.toAdjunction
  haveI : (ihom X).Full := Functor.Full.of_iso e.symm
  haveI : (ihom X).Faithful := Functor.Faithful.of_iso e.symm
  haveI : IsIso (ihom.adjunction X).counit := Adjunction.counit_isIso_of_R_fully_faithful _
  exact NatIso.isIso_app_of_isIso (ihom.adjunction X).counit N

theorem whiskerRight_eq_zero_iff {L M Z : Y.Modules} (hZ : Scheme.Modules.IsInvertible Z) (f : L ⟶ M) :
    f ▷ Z = 0 ↔ f = 0 := by
  haveI := isEquivalence_tensorRight hZ
  constructor
  · intro h
    apply (tensorRight Z).map_injective
    rw [Functor.map_zero]
    exact h
  · rintro rfl
    exact (tensorRight Z).map_zero _ _

theorem transposeSection_eq_zero_iff' {X M : Y.Modules} (hX : Scheme.Modules.IsInvertible X) (φ : X ⟶ M)
    (s : 𝟙_ Y.Modules ⟶ M ⊗ Scheme.Modules.dual X)
    (hs : (ihom.ev X).app (𝟙_ Y.Modules) ≫ s = φ ▷ Scheme.Modules.dual X) :
    s = 0 ↔ φ = 0 := by

  have hiso := isIso_ev_app X hX (𝟙_ Y.Modules)
  rw [← whiskerRight_eq_zero_iff hX.dual.1 φ, ← hs]
  exact (@Preadditive.IsIso.comp_left_eq_zero _ _ _ _ _ _ _ s hiso).symm

theorem pullbackSection_transposeSection_eq_zero_iff' {Y' : Scheme.{u}} (g : Y' ⟶ Y) {X M : Y.Modules}
    (hX : Scheme.Modules.IsInvertible X) (φ : X ⟶ M)
    (s : 𝟙_ Y.Modules ⟶ M ⊗ Scheme.Modules.dual X)
    (hs : (ihom.ev X).app (𝟙_ Y.Modules) ≫ s = φ ▷ Scheme.Modules.dual X) :
    Scheme.Modules.pullbackSection g s = 0 ↔ (Scheme.Modules.pullback g).map φ = 0 := by
  have hiso := isIso_ev_app X hX (𝟙_ Y.Modules)
  have hiso' : IsIso ((Scheme.Modules.pullback g).map ((ihom.ev X).app (𝟙_ Y.Modules))) :=
    let e := (Scheme.Modules.pullback g).mapIso (@asIso _ _ _ _ ((ihom.ev X).app (𝟙_ Y.Modules)) hiso)
    ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  have h1 : (Scheme.Modules.pullback g).map ((ihom.ev X).app (𝟙_ Y.Modules)) ≫ (Scheme.Modules.pullback g).map s
      = (Scheme.Modules.pullback g).map (φ ▷ Scheme.Modules.dual X) :=
    ((Scheme.Modules.pullback g).map_comp _ _).symm.trans (congrArg _ hs)
  calc Scheme.Modules.pullbackSection g s = 0
      ↔ (Scheme.Modules.pullback g).map s = 0 := by
        rw [Scheme.Modules.pullbackSection_def]
        exact Preadditive.IsIso.comp_left_eq_zero _ _
    _ ↔ (Scheme.Modules.pullback g).map ((ihom.ev X).app (𝟙_ Y.Modules)) ≫ (Scheme.Modules.pullback g).map s = 0 :=
        (@Preadditive.IsIso.comp_left_eq_zero _ _ _ _ _ _ _ _ hiso').symm
    _ ↔ (Scheme.Modules.pullback g).map (φ ▷ Scheme.Modules.dual X) = 0 :=
        iff_of_eq (congrArg (fun t => t = 0) h1)
    _ ↔ Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) X (Scheme.Modules.dual X) ≫
          ((Scheme.Modules.pullback g).map φ ▷ (Scheme.Modules.pullback g).obj (Scheme.Modules.dual X)) ≫
          Functor.LaxMonoidal.μ (Scheme.Modules.pullback g) M (Scheme.Modules.dual X) = 0 :=
        iff_of_eq (congrArg (fun t => t = 0) (Functor.Monoidal.map_whiskerRight _ _ _))
    _ ↔ ((Scheme.Modules.pullback g).map φ ▷ (Scheme.Modules.pullback g).obj (Scheme.Modules.dual X)) ≫
          Functor.LaxMonoidal.μ (Scheme.Modules.pullback g) M (Scheme.Modules.dual X) = 0 :=
        Preadditive.IsIso.comp_left_eq_zero _ _
    _ ↔ (Scheme.Modules.pullback g).map φ ▷ (Scheme.Modules.pullback g).obj (Scheme.Modules.dual X) = 0 :=
        Preadditive.IsIso.comp_right_eq_zero _ _
    _ ↔ (Scheme.Modules.pullback g).map φ = 0 := whiskerRight_eq_zero_iff (hX.dual.1.pullback g) _

end AlgebraicGeometry.Scheme.Modules.CoevAux

open CategoryTheory CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff.AlgebraicGeometry in
theorem solution
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) {X M : Y.Modules} (hX : Scheme.Modules.IsInvertible X) (φ : X ⟶ M)
    (s : 𝟙_ Y.Modules ⟶ M ⊗ Scheme.Modules.dual X)
    (hs : (ihom.ev X).app (𝟙_ Y.Modules) ≫ s = φ ▷ Scheme.Modules.dual X) :
    Scheme.Modules.pullbackSection g s = 0 ↔ (Scheme.Modules.pullback g).map φ = 0 :=
  AlgebraicGeometry.Scheme.Modules.CoevAux.pullbackSection_transposeSection_eq_zero_iff' g hX φ s hs

end
end E6Coev

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff (solution)

-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:44:57.007772+00:00
-- url     : https://prove2.me/theorems/7b559094-fc35-4a45-b147-79e757fcd22b
-- title:
--   Derivative Ideal Sheaf
-- statement:
--   Definitions and structural lemmas for Derivative Ideal Sheaf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheaf.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_derivIdeal_away

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
theorem le_preimage_top (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    U ≤ p ⁻¹ᵁ ⊤ := by
  intro _ _
  trivial
noncomputable def sectionsAlgebraMap (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) : k →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U)).hom
theorem sectionsAlgebraMap_eq (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    sectionsAlgebraMap k p U =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U)).hom :=
  rfl
theorem sectionsAlgebraMap_comp_restrict (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) {U V : X.Opens} (h : V ≤ U) :
    (X.presheaf.map (homOfLE h).op).hom.comp (sectionsAlgebraMap k p U) =
      sectionsAlgebraMap k p V := by
  have key : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U)) ≫
      X.presheaf.map (homOfLE h).op =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V (le_preimage_top k p V) := by
    rw [Category.assoc, Scheme.Hom.appLE_map]
  rw [sectionsAlgebraMap_eq k p U, sectionsAlgebraMap_eq k p V, ← CommRingCat.hom_comp, key]
theorem sectionsAlgebraMap_restrict_apply (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) {U V : X.Opens} (h : V ≤ U) (a : k) :
    (X.presheaf.map (homOfLE h).op).hom (sectionsAlgebraMap k p U a) =
      sectionsAlgebraMap k p V a :=
  DFunLike.congr_fun (sectionsAlgebraMap_comp_restrict k p h) a
@[reducible] noncomputable def sectionsAlgebra (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) : Algebra k Γ(X, U) :=
  (sectionsAlgebraMap k p U).toAlgebra
theorem isScalarTower_sections (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (f : Γ(X, U))
    [Algebra k Γ(X, U)] [Algebra k Γ(X, X.basicOpen f)]
    [Algebra Γ(X, U) Γ(X, X.basicOpen f)]
    (hU : algebraMap k Γ(X, U) = sectionsAlgebraMap k p U)
    (hV : algebraMap k Γ(X, X.basicOpen f) = sectionsAlgebraMap k p (X.basicOpen f))
    (hres : algebraMap Γ(X, U) Γ(X, X.basicOpen f) =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom) :
    IsScalarTower k Γ(X, U) Γ(X, X.basicOpen f) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [hV, hres, hU, sectionsAlgebraMap_restrict_apply]
theorem finiteType_sections (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (U : X.affineOpens)
    [Algebra k Γ(X, U.1)] (h : algebraMap k Γ(X, U.1) = sectionsAlgebraMap k p U.1) :
    Algebra.FiniteType k Γ(X, U.1) := by
  have hft : (p.appLE ⊤ U.1 (le_preimage_top k p U.1)).hom.FiniteType := by
    apply Scheme.Hom.finiteType_appLE p (isAffineOpen_top _) U.2
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id]
  have hsurj : Function.Surjective ⇑(Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom := fun y =>
    ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom y, DFunLike.congr_fun hcomp y⟩
  have hiso : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ hsurj
  have hst : (sectionsAlgebraMap k p U.1).FiniteType := by
    rw [sectionsAlgebraMap_eq, CommRingCat.hom_comp]
    exact hft.comp hiso
  have hinst : ‹Algebra k Γ(X, U.1)› = (sectionsAlgebraMap k p U.1).toAlgebra :=
    Algebra.algebra_ext _ _ fun r => DFunLike.congr_fun h r
  rw [hinst]
  exact hst
theorem isNoetherianRing_sections (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (U : X.affineOpens)
    [Algebra k Γ(X, U.1)] (h : algebraMap k Γ(X, U.1) = sectionsAlgebraMap k p U.1) :
    IsNoetherianRing Γ(X, U.1) := by
  have : Algebra.FiniteType k Γ(X, U.1) := finiteType_sections k p U h
  exact Algebra.FiniteType.isNoetherianRing k Γ(X, U.1)
theorem finitePresentation_kaehlerDifferential_sections (k : Type u) [CommRing k]
    [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] (U : X.affineOpens) [Algebra k Γ(X, U.1)]
    (h : algebraMap k Γ(X, U.1) = sectionsAlgebraMap k p U.1) :
    Module.FinitePresentation Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) := by
  have : Algebra.FiniteType k Γ(X, U.1) := finiteType_sections k p U h
  have : IsNoetherianRing Γ(X, U.1) := isNoetherianRing_sections k p U h
  have : Module.Finite Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) := inferInstance
  exact Module.finitePresentation_of_finite ..
theorem derivIdealSheaf_map_ideal_basicOpen (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) :
    ∀ (U : X.affineOpens) (f : Γ(X, U.1)),
      Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
          (@derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U)) =
        @derivIdeal k _ _ _ (sectionsAlgebra k p (X.affineBasicOpen f).1)
          (I.ideal (X.affineBasicOpen f)) := by
  intro U f
  let algU : Algebra k Γ(X, U.1) := sectionsAlgebra k p U.1
  let algV : Algebra k Γ(X, X.basicOpen f) := sectionsAlgebra k p (X.basicOpen f)
  let algUV : Algebra Γ(X, U.1) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  have htower : IsScalarTower k Γ(X, U.1) Γ(X, X.basicOpen f) :=
    isScalarTower_sections k p U.1 f rfl rfl rfl
  have hloc : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  have hfp : Module.FinitePresentation Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) :=
    finitePresentation_kaehlerDifferential_sections k p U rfl
  have hI : Ideal.map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f)) (I.ideal U) =
      I.ideal (X.affineBasicOpen f) := I.map_ideal_basicOpen U f
  have key := map_derivIdeal_away (k := k) (S' := Γ(X, X.basicOpen f)) f (I.ideal U)
  exact key.trans (congrArg (@derivIdeal k _ Γ(X, X.basicOpen f) _ algV) hI)
noncomputable def derivIdealSheaf (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData) :
    X.IdealSheafData where
  ideal U := @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U)
  map_ideal_basicOpen := derivIdealSheaf_map_ideal_basicOpen k p I
noncomputable def derivIdealSheafIterate (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    ℕ → X.IdealSheafData → X.IdealSheafData
  | 0, I => I
  | (r + 1), I => derivIdealSheaf k p (derivIdealSheafIterate k p r I)
end FunctorialResolution.EmbeddedResolution



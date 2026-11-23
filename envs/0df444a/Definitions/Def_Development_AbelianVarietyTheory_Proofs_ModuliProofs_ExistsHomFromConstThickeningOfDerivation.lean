-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHomFromConstThickeningOfDerivation
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHomFromConstThickeningOfDerivation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:43.423103+00:00
-- url     : https://prove2.me/theorems/49d652bf-7e67-4558-b0bc-c3fef2bfea86
-- title:
--   Exists Hom From Const Thickening Of Derivation
-- statement:
--   Definitions and structural lemmas for Exists Hom From Const Thickening Of Derivation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHomFromConstThickeningOfDerivation.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.DerMor
def preHom {Z X : Scheme.{0}} (n : Z ⟶ X) (c : ∀ W : X.Opens, Γ(X, W) →+* Γ(Z, n ⁻¹ᵁ W))
    (hres : ∀ W W' (h : W' ≤ W) f, c W' (resG X h f) = resG Z (fun _ hy => h hy) (c W f)) :
    Z.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := n.base
  c :=
    { app := fun W => CommRingCat.ofHom (c W.unop)
      naturality := fun W W' i => by
        ext f
        exact hres W.unop W'.unop i.unop.le f }
def deform {Z X : Scheme.{0}} (n : Z ⟶ X) (c : ∀ W : X.Opens, Γ(X, W) →+* Γ(Z, n ⁻¹ᵁ W))
    (hres : ∀ W W' (h : W' ≤ W) f, c W' (resG X h f) = resG Z (fun _ hy => h hy) (c W f))
    (hnil : ∀ W f, IsNilpotent (c W f - (n.app W).hom f)) : Z ⟶ X :=
  ⟨⟨preHom n c hres, fun x => ⟨fun a ha => by
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf a
    have hU' : n x ∈ U := hU
    have h1 := PresheafedSpace.stalkMap_germ_apply (preHom n c hres) U x hU s
    have h2 : IsUnit ((Z.presheaf.germ (n ⁻¹ᵁ U) x hU').hom (c U s)) := by
      have ha' := ha
      erw [h1] at ha'
      exact ha'
    have h3 : IsUnit ((Z.presheaf.germ (n ⁻¹ᵁ U) x hU').hom ((n.app U).hom s)) := by
      have hn := ((hnil U s).map (Z.presheaf.germ (n ⁻¹ᵁ U) x hU').hom).neg
      have := hn.isUnit_add_left_of_commute h2 (Commute.all _ _)
      simpa using this
    have h4 := Scheme.Hom.germ_stalkMap_apply n U x hU' s
    have h5 : IsUnit ((n.stalkMap x).hom ((X.presheaf.germ U (n x) hU').hom s)) := by
      erw [h4]
      exact h3
    exact (isUnit_map_iff (n.stalkMap x).hom _).mp h5⟩⟩⟩
def cH {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top).hom
def pert {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) (e : C)
    (he : e * e = 0) (d : A → B) (hadd : ∀ f f', d (f + f') = d f + d f')
    (hmul : ∀ f f', d (f * f') = a f * d f' + a f' * d f) : A →+* C where
  toFun f := b (a f) + e * b (d f)
  map_one' := by
    have h := hmul 1 1
    rw [show (1 : A) * 1 = 1 from mul_one 1, map_one] at h
    have h1 : d 1 = 0 := by linear_combination -h
    simp [h1]
  map_zero' := by
    have h := hadd 0 0
    simp only [add_zero] at h
    have h1 : d 0 = 0 := by linear_combination -h
    simp [h1]
  map_add' f f' := by
    simp only [hadd, map_add]; ring
  map_mul' f f' := by
    simp only [hmul, map_add, map_mul]
    linear_combination (-(b (d f) * b (d f'))) * he
end GlobalTheory.KS.DerMor
end



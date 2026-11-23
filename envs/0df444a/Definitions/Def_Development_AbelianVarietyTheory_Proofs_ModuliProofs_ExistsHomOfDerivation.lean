-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHomOfDerivation
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHomOfDerivation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:13.867052+00:00
-- url     : https://prove2.me/theorems/2d8ec1d4-962d-41a0-b1db-d98a3d03c022
-- title:
--   Exists Hom Of Derivation
-- statement:
--   Definitions and structural lemmas for Exists Hom Of Derivation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHomOfDerivation.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
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
namespace GlobalTheory.KS.DerMorK
section Deform
variable {Z X : Scheme.{0}} (g : Z ⟶ X) (ψ : ∀ W : X.Opens, Γ(X, W) →+* Γ(Z, g ⁻¹ᵁ W))
  (hnat : ∀ (W W' : X.Opens) (h : W' ≤ W) (f : Γ(X, W)),
    ψ W' (resG X h f) = resG Z (g.preimage_mono h) (ψ W f))
def deformPsh : Z.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := g.base
  c :=
    { app := fun W => CommRingCat.ofHom (ψ W.unop)
      naturality := fun W W' i => by
        ext f
        exact hnat W.unop W'.unop i.unop.le f }
def deformHom (hnil : ∀ (W : X.Opens) (f : Γ(X, W)), IsNilpotent (ψ W f - (g.app W).hom f)) : Z ⟶ X :=
  ⟨⟨deformPsh g ψ hnat, fun x => ⟨fun a ha => by
    obtain ⟨W, hW, f, rfl⟩ := X.presheaf.germ_exist a
    have h1 := PresheafedSpace.stalkMap_germ_apply (deformPsh g ψ hnat) W x hW f
    have h2 := Scheme.Hom.germ_stalkMap_apply g W x hW f
    have h3 : IsNilpotent ((Z.presheaf.germ (g ⁻¹ᵁ W) x hW).hom (ψ W f - (g.app W).hom f)) :=
      (hnil W f).map _
    have h4 : IsUnit ((Z.presheaf.germ (g ⁻¹ᵁ W) x hW).hom (ψ W f)) := by
      erw [h1] at ha
      exact ha
    have h5 : IsUnit ((Z.presheaf.germ (g ⁻¹ᵁ W) x hW).hom ((g.app W).hom f)) := by
      have := h3.neg.isUnit_add_right_of_commute h4 (Commute.all _ _)
      rw [map_sub] at this
      convert this using 1
      ring
    rw [← h2] at h5
    exact isUnit_of_map_unit (g.stalkMap x).hom _ h5⟩⟩⟩
end Deform
def constHom {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
theorem constFn_eq {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a : R) :
    constFn p U a = constHom p U a := rfl
section Main
variable {K : Type} [Field K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K} (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y)
  {R : Type} [CommRing R] {D : R → K} {X : Scheme.{0}} {p : X ⟶ Sp R} {m : Y ⟶ X}
  {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
theorem eps_sq (U : Y'.Opens) :
    constFn π U DualNumber.eps * constFn π U DualNumber.eps = 0 := by
  rw [constFn_eq, ← map_mul, DualNumber.eps_mul_eps, map_zero]
def psi (hd : LocDerK q p m D ⊤ d) (W : X.Opens) : Γ(X, W) →+* Γ(Y', (ρ ≫ m) ⁻¹ᵁ W) where
  toFun f := (ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f) +
    constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W) DualNumber.eps * (ρ.app (m ⁻¹ᵁ W)).hom (d W f)
  map_one' := by
    have h := hd.mul W le_top 1 1
    simp only [_root_.mul_one, map_one, _root_.one_mul] at h
    have h0 : d W 1 = 0 := by linear_combination -h
    simp only [h0, map_one, map_zero, mul_zero, add_zero]
    rfl
  map_mul' f f' := by
    have h := eps_sq π (ρ ⁻¹ᵁ m ⁻¹ᵁ W)
    rw [hd.mul W le_top]
    simp only [map_mul, map_add]
    change (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) = (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) * (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W))
    linear_combination -((ρ.app (m ⁻¹ᵁ W)).hom (d W f) * (ρ.app (m ⁻¹ᵁ W)).hom (d W f')) * h
  map_zero' := by
    have h := hd.add W le_top 0 0
    simp only [add_zero] at h
    have h0 : d W 0 = 0 := by linear_combination -h
    simp only [h0, map_zero, mul_zero, add_zero]
    rfl
  map_add' f f' := by
    rw [hd.add W le_top]
    simp only [map_add]
    change (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) = (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) + (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W))
    ring
end Main
end GlobalTheory.KS.DerMorK
end



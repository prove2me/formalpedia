-- Prove2me | Definitions.Def_MazurTransfer_OriginalRelativeNormKernelSchemePointsAndGroupLawData20261020
-- name    : MazurTransfer_OriginalRelativeNormKernelSchemePointsAndGroupLawData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T00:51:33.176966+00:00
-- url     : https://prove2.me/theorems/23d4f8b7-6b23-4c19-a8d2-038ac174156e
-- title:
--   Original relative norm kernel scheme, points and group law
-- statement:
--   Retain the scheme-theoretic kernel of the given relative group endomorphism, its original point equivalence and intrinsic naturality certificate, kernel multiplication and inversion certificates, inherited relative group law and finite-free model predicate. All sixteen complete original types, ten whole constructor values and nineteen generated structural proof types are independently checked. Hopf existence and commutativity are separate theorem interfaces. Named downstream consumer: the actual integral nineteen norm kernel and its same norm-preimage torsors.
-- source:
--   MazurTheorem RelativeGroupLawFiniteFlatKernelHopf by Vas and contributors; original constructor interface retaining the Apache-2.0 attribution of its exact official Anthropic FLT input.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The kernel group-law and Hopf representability construction adapts the
complete official Anthropic FLT scalar-kernel proof at
6e837e75355538c7f80bab5b956861e86c4eacc2 to a relative group endomorphism.
Design boundary: the ACTUAL scheme-theoretic kernel of a finite-flat
relative endomorphism, with its algebra-valued points, multiplication
and all coefficient base changes; the map must preserve the given law.
The intrinsic kernel membership, point comparison and group preservation certificates construct the same kernel data; Hopf model existence is a separate theorem interface.
Named downstream consumer: the two actual integral nineteen norm kernels.
-/
import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

noncomputable section
namespace MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GoodReductionJacobian NeronModelInfra
open scoped CategoryTheory.MonObj
universe u
variable {R : Type u} [CommRing R] {A : Scheme.{u}}
variable {f : A ⟶ Spec (CommRingCat.of R)}
variable (L : RelativeGroupLaw R f) (F : SchemeHomOver f f)

abbrev kernelScheme : Scheme.{u} := pullback F.val (L.one (𝟙 (Spec (CommRingCat.of R)))).val
abbrev kernelStr : kernelScheme L F ⟶ Spec (CommRingCat.of R) := pullback.snd _ _
abbrev kernelIncl : kernelScheme L F ⟶ A := pullback.fst _ _

abbrev kernelPoints {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :=
  {x : SchemeHomOver t f // NeronModelInfra.schemeHomOverComp x F = L.one t}

theorem kernelIncl_over : kernelIncl L F ≫ f = kernelStr L F := by
  have h1 : kernelIncl L F ≫ F.val =
      kernelStr L F ≫ (L.one (𝟙 _)).val := pullback.condition
  have h2 : (kernelIncl L F ≫ F.val) ≫ f = kernelIncl L F ≫ f := by
    rw [Category.assoc, F.property]
  rw [h1, Category.assoc, (L.one (𝟙 _)).property, Category.comp_id] at h2
  exact h2.symm

theorem one_coe_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).val = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).val := by
  have h := L.one_natural (𝟙 _) t t (Category.comp_id t)
  rw [← h]; rfl

section Points
variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
def kernelPointToBase (a : SchemeHomOver t (kernelStr L F)) : SchemeHomOver t f :=
  ⟨a.val ≫ kernelIncl L F, by rw [Category.assoc, kernelIncl_over, a.property]⟩

theorem kernelPointToBase_mem (a : SchemeHomOver t (kernelStr L F)) :
    NeronModelInfra.schemeHomOverComp (kernelPointToBase L F t a) F = L.one t := by
  apply Subtype.ext
  change (a.val ≫ kernelIncl L F) ≫ F.val = (L.one t).val
  rw [one_coe_eq, Category.assoc, pullback.condition, ← Category.assoc, a.property]

def kernelPointsForward (a : SchemeHomOver t (kernelStr L F)) : kernelPoints L F t :=
  ⟨kernelPointToBase L F t a, kernelPointToBase_mem L F t a⟩

def kernelPointsBackward (x : kernelPoints L F t) : SchemeHomOver t (kernelStr L F) :=
  ⟨pullback.lift x.val.val t (by
    have hx := congrArg Subtype.val x.property
    change x.val.val ≫ F.val = (L.one t).val at hx
    exact hx.trans (one_coe_eq L t)), pullback.lift_snd _ _ _⟩

def kernelPointsEquiv : SchemeHomOver t (kernelStr L F) ≃ kernelPoints L F t where
  toFun := kernelPointsForward L F t
  invFun := kernelPointsBackward L F t
  left_inv a := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans a.property.symm
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact pullback.lift_fst _ _ _

theorem kernelPointsEquiv_natural {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (a : SchemeHomOver t (kernelStr L F)) :
    (kernelPointsEquiv L F t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a)).val =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (kernelPointsEquiv L F t a).val := by
  apply Subtype.ext
  exact Category.assoc _ _ _
end Points

variable
  (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t)
  (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (L.mul t x y) F =
      L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F))

include hMul in
theorem kernelPoints_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : kernelPoints L F t) :
    NeronModelInfra.schemeHomOverComp (L.mul t x.val y.val) F = L.one t := by
  rw [hMul, x.property, y.property, L.one_mul]

include hOne hMul in
theorem kernelPoints_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : kernelPoints L F t) :
    NeronModelInfra.schemeHomOverComp (L.inv t x.val) F = L.one t := by
  have h := hMul t x.val (L.inv t x.val)
  rw [L.mul_inv_cancel, hOne, x.property, L.one_mul] at h
  exact h.symm

def kernelLaw : RelativeGroupLaw R (kernelStr L F) where
  mul t x y := (kernelPointsEquiv L F t).symm
    ⟨L.mul t (kernelPointsEquiv L F t x).val (kernelPointsEquiv L F t y).val,
      kernelPoints_mul L F hMul t _ _⟩
  one t := (kernelPointsEquiv L F t).symm ⟨L.one t, hOne t⟩
  inv t x := (kernelPointsEquiv L F t).symm
    ⟨L.inv t (kernelPointsEquiv L F t x).val, kernelPoints_inv L F hOne hMul t _⟩
  mul_assoc t x y z := (kernelPointsEquiv L F t).injective (by
    simp only [Equiv.apply_symm_apply]
    exact Subtype.ext (L.mul_assoc t _ _ _))
  one_mul t x := (kernelPointsEquiv L F t).injective (by
    simp only [Equiv.apply_symm_apply]
    exact Subtype.ext (L.one_mul t _))
  mul_one t x := (kernelPointsEquiv L F t).injective (by
    simp only [Equiv.apply_symm_apply]
    exact Subtype.ext (L.mul_one t _))
  inv_mul_cancel t x := (kernelPointsEquiv L F t).injective (by
    simp only [Equiv.apply_symm_apply]
    exact Subtype.ext (L.inv_mul_cancel t _))
  mul_natural t t' ψ hψ x y := (kernelPointsEquiv L F t').injective (by
    apply Subtype.ext
    rw [Subtype.val, Equiv.apply_symm_apply]
    show (kernelPointsEquiv L F t' (GoodReductionJacobian.schemeHomOverComp ψ hψ
      ((kernelPointsEquiv L F t).symm _))).val =
      L.mul t' (kernelPointsEquiv L F t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)).val
        (kernelPointsEquiv L F t' (GoodReductionJacobian.schemeHomOverComp ψ hψ y)).val
    rw [kernelPointsEquiv_natural, Equiv.apply_symm_apply,
      kernelPointsEquiv_natural, kernelPointsEquiv_natural]
    exact L.mul_natural t t' ψ hψ _ _)





def HasFiniteFreeKernelHopfModel : Prop :=
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H),
      ∃ (_ : Module.Finite R H) (_ : Module.Free R H) (_ : Coalgebra.IsCocomm R H),
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra R T],
          WithConv (H →ₐ[R] T) ≃ kernelPoints L F (Spec.map (CommRingCat.ofHom (algebraMap R T))),
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
          (e T (φ * ψ)).val = L.mul _ (e T φ).val (e T ψ).val) ∧
        (∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
            (g : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
          (e T' (.toConv (g.comp φ.ofConv))).val.val =
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.val)



end MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf

#print axioms MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf.kernelScheme
#print axioms MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf.kernelStr
#print axioms MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf.kernelIncl
#print axioms MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf.kernelPoints
#print axioms MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf.kernelIncl_over
#print axioms MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf.one_coe_eq
#print axioms MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf.kernelPointToBase
#print axioms MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf.kernelPointToBase_mem
#print axioms MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf.kernelPointsForward
#print axioms MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf.kernelPointsBackward
#print axioms MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf.kernelPointsEquiv
#print axioms MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf.kernelPointsEquiv_natural
#print axioms MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf.kernelPoints_mul
#print axioms MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf.kernelPoints_inv
#print axioms MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf.kernelLaw
#print axioms MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf.HasFiniteFreeKernelHopfModel



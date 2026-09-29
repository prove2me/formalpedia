-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.exists_overlap_iso_isTangentCoordsOfPairAtVia_of_pointDerivations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7380b916-3d27-5c37-b94f-8cc6d2de5cc8

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations

import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAtVia_of_pointDerivations
import Theorems.Thm_AlgebraicGeometry_exists_iso_of_specMap_quotient_comp_eq_fromSpec
import Theorems.Thm_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_exists_overlap_iso_isTangentCoordsOfPairAtVia_of_pointDerivations

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace TwistPairAux

theorem fromSpec_comp_eq {T' : Type u} [CommRing T'] {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T')) (U : Y.Opens) (hU : IsAffineOpen U) :
    letI := algebraOfHom q U
    hU.fromSpec ≫ q = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y, U))) := by
  letI := algebraOfHom q U
  rw [show CommRingCat.ofHom (algebraMap T' Γ(Y, U)) = (Scheme.ΓSpecIso (CommRingCat.of T')).inv ≫ q.appLE ⊤ U le_top from rfl,
    Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hU le_top]

theorem flat_sections {T' : Type u} [CommRing T'] {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T')) [Flat q] (U : Y.Opens) (hU : IsAffineOpen U) :
    letI := algebraOfHom q U
    Module.Flat T' Γ(Y, U) := by
  have h1 : (q.appLE ⊤ U le_top).hom.Flat := HasRingHomProperty.appLE @Flat q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of T')).inv ≫ q.appLE ⊤ U le_top).hom.Flat :=
    RingHom.Flat.comp (.of_bijective (Scheme.ΓSpecIso (CommRingCat.of T')).symm.commRingCatIsoToRingEquiv.bijective) h1
  exact h2

end TwistPairAux

open TwistPairAux

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    (hI : RingHom.ker π ≤ maximalIdeal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T))
    (Ua Ub : A₀.Opens)
    {Ya Yb : Scheme.{u}} (qa : Ya ⟶ Spec (CommRingCat.of T')) (qb : Yb ⟶ Spec (CommRingCat.of T')) (hqa : Smooth qa)
    (ga : (↑Ua : Scheme.{u}) ⟶ Ya) (gb : (↑Ub : Scheme.{u}) ⟶ Yb)
    (hgb : IsPullback gb (Ub.ι ≫ f₀) qb (Spec.map (CommRingCat.ofHom π)))
    (Oa : A₀.Opens → Ya.Opens) (Ob : A₀.Opens → Yb.Opens)
    (hOb : ∀ W : A₀.Opens, gb ⁻¹ᵁ Ob W = Ub.ι ⁻¹ᵁ W)
    (hOaffa : IsAffineOpen (Oa (Ua ⊓ Ub))) (hOaffb : IsAffineOpen (Ob (Ua ⊓ Ub)))

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') fk)
    (W : Ak.Opens) (aW : (W : Scheme.{u}) ⟶ Yb)
    (haW : IsPullback aW (W.ι ≫ fk) qb (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    (φ : (↑(Oa (Ua ⊓ Ub)) : Scheme.{u}) ≅ ↑(Ob (Ua ⊓ Ub)))
    (hφq : φ.hom ≫ (Ob (Ua ⊓ Ub)).ι ≫ qb = (Oa (Ua ⊓ Ub)).ι ≫ qa)
    (hφg : ∃ (γ : (↑(Ua ⊓ Ub) : Scheme.{u}) ⟶ ↑(Oa (Ua ⊓ Ub))) (γ' : (↑(Ua ⊓ Ub) : Scheme.{u}) ⟶ ↑(Ob (Ua ⊓ Ub))),
        γ ≫ (Oa (Ua ⊓ Ub)).ι = A₀.homOfLE inf_le_left ≫ ga ∧
        γ' ≫ (Ob (Ua ⊓ Ub)).ι = A₀.homOfLE inf_le_right ≫ gb ∧
        γ ≫ φ.hom = γ')
    (hφO : ∀ W' : A₀.Opens, φ.hom ⁻¹ᵁ ((Ob (Ua ⊓ Ub)).ι ⁻¹ᵁ Ob W') = (Oa (Ua ⊓ Ub)).ι ⁻¹ᵁ Oa W')

    (δ : letI := algebraOfHom qa (Oa (Ua ⊓ Ub)); letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(Ya, Oa (Ua ⊓ Ub)))))) :
    letI := algebraOfHom qa (Oa (Ua ⊓ Ub)); letI := algebraOfHom fk Ue
    ∃ φ' : (↑(Oa (Ua ⊓ Ub)) : Scheme.{u}) ≅ ↑(Ob (Ua ⊓ Ub)),
      φ'.hom ≫ (Ob (Ua ⊓ Ub)).ι ≫ qb = (Oa (Ua ⊓ Ub)).ι ≫ qa ∧
      (∃ (γ : (↑(Ua ⊓ Ub) : Scheme.{u}) ⟶ ↑(Oa (Ua ⊓ Ub))) (γ' : (↑(Ua ⊓ Ub) : Scheme.{u}) ⟶ ↑(Ob (Ua ⊓ Ub))),
        γ ≫ (Oa (Ua ⊓ Ub)).ι = A₀.homOfLE inf_le_left ≫ ga ∧
        γ' ≫ (Ob (Ua ⊓ Ub)).ι = A₀.homOfLE inf_le_right ≫ gb ∧
        γ ≫ φ'.hom = γ') ∧
      (∀ W' : A₀.Opens, φ'.hom ⁻¹ᵁ ((Ob (Ua ⊓ Ub)).ι ⁻¹ᵁ Ob W') = (Oa (Ua ⊓ Ub)).ι ⁻¹ᵁ Oa W') ∧
      IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Ya, Oa (Ua ⊓ Ub))
        (hOaffa.isoSpec.inv ≫ φ.hom ≫ (Ob (Ua ⊓ Ub)).ι)
        (hOaffa.isoSpec.inv ≫ φ'.hom ≫ (Ob (Ua ⊓ Ub)).ι)
        fk Lk W aW Ue
        (fun x => (δ : Γ(Ak, Ue) →ₗ[ResidueField T']
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(Ya, Oa (Ua ⊓ Ub))))) x) := by
  classical
  letI instA : Algebra T' Γ(Ya, Oa (Ua ⊓ Ub)) := algebraOfHom qa (Oa (Ua ⊓ Ub))
  letI instB : Algebra T' Γ(Yb, Ob (Ua ⊓ Ub)) := algebraOfHom qb (Ob (Ua ⊓ Ub))
  letI instE : Algebra (ResidueField T') Γ(Ak, Ue) := algebraOfHom fk Ue
  haveI := hqa
  haveI : Module.Flat T' Γ(Ya, Oa (Ua ⊓ Ub)) := flat_sections qa (Oa (Ua ⊓ Ub)) hOaffa
  have hI2 : RingHom.ker π * RingHom.ker π = ⊥ := le_bot_iff.mp ((Ideal.mul_mono_right hI).trans hsmall.le)

  have hstra := fromSpec_comp_eq qa (Oa (Ua ⊓ Ub)) hOaffa
  have hstrb := fromSpec_comp_eq qb (Ob (Ua ⊓ Ub)) hOaffb

  have hu : (hOaffa.isoSpec.inv ≫ φ.hom ≫ (Ob (Ua ⊓ Ub)).ι) ≫ qb =
      Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Ya, Oa (Ua ⊓ Ub)))) := by
    rw [Category.assoc, Category.assoc, hφq, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι, hstra]

  obtain ⟨v, hv, huv, hvia⟩ :=
    AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAtVia_of_pointDerivations (RingHom.ker π) hI hsmall V ι hι hιI
      (Ya.presheaf.obj (Opposite.op (Oa (Ua ⊓ Ub)))) qb (hOaffa.isoSpec.inv ≫ φ.hom ≫ (Ob (Ua ⊓ Ub)).ι) hu fk Lk W aW haW
      Ue hUe e₁ he₁ δ

  let X : Spec Γ(Ya, Oa (Ua ⊓ Ub)) ⟶ Spec Γ(Yb, Ob (Ua ⊓ Ub)) := hOaffa.isoSpec.inv ≫ φ.hom ≫ hOaffb.isoSpec.hom
  let Xi : Spec Γ(Yb, Ob (Ua ⊓ Ub)) ⟶ Spec Γ(Ya, Oa (Ua ⊓ Ub)) := hOaffb.isoSpec.inv ≫ φ.inv ≫ hOaffa.isoSpec.hom
  have hXXi : X ≫ Xi = 𝟙 _ := by
    simp only [X, Xi, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]
  have hXiX : Xi ≫ X = 𝟙 _ := by
    simp only [X, Xi, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  have hXchart : X ≫ hOaffb.fromSpec = hOaffa.isoSpec.inv ≫ φ.hom ≫ (Ob (Ua ⊓ Ub)).ι := by
    simp only [X, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc]

  have hXiT : Xi ≫ Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Ya, Oa (Ua ⊓ Ub)))) =
      Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Yb, Ob (Ua ⊓ Ub)))) := by
    rw [← hstra, ← hstrb, ← IsAffineOpen.isoSpec_inv_ι, ← IsAffineOpen.isoSpec_inv_ι]
    simp only [Xi, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← hφq]
    simp only [Iso.inv_hom_id_assoc]

  let ψ₀ : Γ(Ya, Oa (Ua ⊓ Ub)) ⟶ Γ(Yb, Ob (Ua ⊓ Ub)) := Spec.preimage Xi
  have hψ₀ : Spec.map ψ₀ = Xi := Spec.map_preimage Xi
  have hψcomm : ∀ t : T', ψ₀.hom (algebraMap T' Γ(Ya, Oa (Ua ⊓ Ub)) t) = algebraMap T' Γ(Yb, Ob (Ua ⊓ Ub)) t := by
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Ya, Oa (Ua ⊓ Ub))) ≫ ψ₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Yb, Ob (Ua ⊓ Ub)))) := by
      rw [Spec.map_comp, hψ₀]; exact hXiT
    have h2 := Spec.map_injective h1
    intro t
    exact congrArg (fun f : CommRingCat.of T' ⟶ Γ(Yb, Ob (Ua ⊓ Ub)) => f.hom t) h2
  let ψ : Γ(Ya, Oa (Ua ⊓ Ub)) →ₐ[T'] Γ(Yb, Ob (Ua ⊓ Ub)) := ⟨ψ₀.hom, hψcomm⟩
  have hIψ : (RingHom.ker π).map (algebraMap T' Γ(Ya, Oa (Ua ⊓ Ub))) ≤
      ((RingHom.ker π).map (algebraMap T' Γ(Yb, Ob (Ua ⊓ Ub)))).comap ψ.toRingHom := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
    intro t ht
    rw [Ideal.mem_comap]
    change ψ (algebraMap T' _ t) ∈ _
    rw [ψ.commutes]
    exact Ideal.mem_map_of_mem _ ht
  let ψbar := Ideal.quotientMap ((RingHom.ker π).map (algebraMap T' Γ(Yb, Ob (Ua ⊓ Ub)))) ψ.toRingHom hIψ
  have hψbar : (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Yb, Ob (Ua ⊓ Ub))))).comp ψ.toRingHom =
      ψbar.comp (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Ya, Oa (Ua ⊓ Ub))))) := by
    ext c; rfl
  have hXired : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Yb, Ob (Ua ⊓ Ub)))))) ≫ Xi =
      Spec.map (CommRingCat.ofHom ψbar) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Ya, Oa (Ua ⊓ Ub)))))) := by
    rw [← hψ₀, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hψbar]
    rfl

  have hvb : (Xi ≫ v) ≫ qb = hOaffb.fromSpec ≫ qb := by
    rw [Category.assoc, hv, hXiT, hstrb]
  have hredb : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Yb, Ob (Ua ⊓ Ub)))))) ≫ Xi ≫ v =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Yb, Ob (Ua ⊓ Ub)))))) ≫ hOaffb.fromSpec := by
    calc Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Yb, Ob (Ua ⊓ Ub)))))) ≫ Xi ≫ v
        = (Spec.map (CommRingCat.ofHom ψbar) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Ya, Oa (Ua ⊓ Ub))))))) ≫ v := by
          rw [← Category.assoc, hXired]
      _ = Spec.map (CommRingCat.ofHom ψbar) ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Ya, Oa (Ua ⊓ Ub)))))) ≫ (hOaffa.isoSpec.inv ≫ φ.hom ≫ (Ob (Ua ⊓ Ub)).ι)) := by
          rw [Category.assoc, huv]
      _ = (Spec.map (CommRingCat.ofHom ψbar) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Ya, Oa (Ua ⊓ Ub))))))) ≫ X ≫ hOaffb.fromSpec := by
          rw [← hXchart]; simp only [X, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Yb, Ob (Ua ⊓ Ub)))))) ≫ (Xi ≫ X) ≫ hOaffb.fromSpec := by
          rw [← hXired]; simp only [Xi, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Yb, Ob (Ua ⊓ Ub)))))) ≫ hOaffb.fromSpec := by
          rw [hXiX]
          erw [Category.id_comp]
  obtain ⟨τ, hτ1, hτ2, hτ3, hτ4⟩ :=
    AlgebraicGeometry.exists_iso_of_specMap_quotient_comp_eq_fromSpec (RingHom.ker π) hI2 qb (Ob (Ua ⊓ Ub)) hOaffb (Xi ≫ v) hvb hredb

  refine ⟨φ ≪≫ τ, ?_, ?_, ?_, ?_⟩
  ·
    rw [Iso.trans_hom, Category.assoc, hτ2, hφq]
  ·
    obtain ⟨γ, γ', hγ, hγ', hγφ⟩ := hφg
    refine ⟨γ, γ', hγ, hγ', ?_⟩
    rw [Iso.trans_hom, ← Category.assoc, hγφ]

    obtain ⟨-, ε, hε⟩ :=
      AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq π hπ hker qb (Ub.ι ≫ f₀) gb hgb (Ob (Ua ⊓ Ub)) hOaffb
    have hrangeκ : Set.range (A₀.homOfLE (inf_le_right : Ua ⊓ Ub ≤ Ub)).base ⊆ Set.range (gb ⁻¹ᵁ Ob (Ua ⊓ Ub)).ι.base := by
      rw [Scheme.Opens.range_ι, hOb, ← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE]
    let κ : (↑(Ua ⊓ Ub) : Scheme.{u}) ⟶ ↑(gb ⁻¹ᵁ Ob (Ua ⊓ Ub)) := IsOpenImmersion.lift (gb ⁻¹ᵁ Ob (Ua ⊓ Ub)).ι (A₀.homOfLE inf_le_right) hrangeκ
    have hκ : κ ≫ (gb ⁻¹ᵁ Ob (Ua ⊓ Ub)).ι = A₀.homOfLE inf_le_right := IsOpenImmersion.lift_fac _ _ _
    have hγ'fac : γ' = κ ≫ (gb ∣_ Ob (Ua ⊓ Ub)) := by
      rw [← cancel_mono (Ob (Ua ⊓ Ub)).ι, hγ', Category.assoc, morphismRestrict_ι, ← Category.assoc, hκ]
    have hres : gb ∣_ Ob (Ua ⊓ Ub) =
        ε.inv ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Yb, Ob (Ua ⊓ Ub)))))) ≫
          hOaffb.isoSpec.inv := by
      rw [← hε, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
    rw [hγ'fac, hres, Category.assoc, Category.assoc, Category.assoc, hτ4]
  ·
    intro W'
    rw [Iso.trans_hom, Scheme.Hom.comp_preimage, hτ3, hφO]
  ·
    have hv' : hOaffa.isoSpec.inv ≫ (φ ≪≫ τ).hom ≫ (Ob (Ua ⊓ Ub)).ι = v := by
      rw [Iso.trans_hom]
      calc hOaffa.isoSpec.inv ≫ (φ.hom ≫ τ.hom) ≫ (Ob (Ua ⊓ Ub)).ι
          = X ≫ (hOaffb.isoSpec.inv ≫ τ.hom ≫ (Ob (Ua ⊓ Ub)).ι) := by
            simp only [X, Category.assoc, Iso.hom_inv_id_assoc]
        _ = X ≫ Xi ≫ v := by rw [hτ1]
        _ = v := by rw [← Category.assoc, hXXi, Category.id_comp]
    rw [hv']
    exact hvia

end S_AlgebraicGeometry_SmallExtension_exists_overlap_iso_isTangentCoordsOfPairAtVia_of_pointDerivations
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_exists_overlap_iso_isTangentCoordsOfPairAtVia_of_pointDerivations (solution)

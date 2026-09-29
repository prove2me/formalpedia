-- Prove2me | solution 1 for AlgebraicGeometry.SplitTorus.existsUnique_muLift_baseChange_of_torusFibre_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7b1bdc7e-3ac7-5617-b38b-88c236cbcb05

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_AlgebraicGeometry_SplitTorus_existsUnique_muLift_of_torusFibre_of_henselian
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_baseChange_schemeNsmul_comp_fst_and_eq_pullback_map
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOver_baseChange_baseChange_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SplitTorus_existsUnique_muLift_baseChange_of_torusFibre_of_henselian
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SplitTorus IsLocalRing

namespace Alpha

theorem exists_transported_torus
    {R₀ A : Type u} [CommRing R₀] [CommRing A] [IsLocalRing A]
    (σ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R₀))
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R₀)) (L : RelativeGroupLaw R₀ g) (t : ℕ)
    (τ : SchemeHomOver (torusStr (ResidueField A) t)
      (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ σ) g))
    (hτ : IsClosedImmersion τ.1)
    (hτmul : ∀ χ χ' : WithConv (torusCoord (ResidueField A) t →ₐ[ResidueField A] ResidueField A),
      NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField A) t (χ * χ').ofConv) τ =
        (L.baseChange (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ σ)).mul _
          (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField A) t χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField A) t χ'.ofConv) τ)) :
    ∃ τ' : SchemeHomOver (torusStr (ResidueField A) t)
        (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
          (RelativeGroupLaw.baseChangeStr σ g)),
      IsClosedImmersion τ'.1 ∧
      (∀ χ χ' : WithConv (torusCoord (ResidueField A) t →ₐ[ResidueField A] ResidueField A),
        NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField A) t (χ * χ').ofConv) τ' =
          ((L.baseChange σ).baseChange (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).mul _
            (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField A) t χ.ofConv) τ')
            (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField A) t χ'.ofConv) τ')) ∧
      τ'.1 ≫ pullback.fst (pullback.snd g σ) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ pullback.fst g σ =
        τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ σ) := by
  obtain ⟨u, v, huv, hvu, hufst, humul⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOver_baseChange_baseChange_iso σ
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) L
  haveI := hτ
  haveI : IsIso v.1 := ⟨⟨u.1, hvu, huv⟩⟩
  haveI : IsIso u.1 := ⟨⟨v.1, huv, hvu⟩⟩
  have hinj : ∀ {s : Spec (CommRingCat.of (ResidueField A)) ⟶ Spec (CommRingCat.of (ResidueField A))}
      (a b : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
        (RelativeGroupLaw.baseChangeStr σ g))),
      NeronModelInfra.schemeHomOverComp a u = NeronModelInfra.schemeHomOverComp b u → a = b := by
    intro s a b hab
    apply Subtype.ext
    have h1 := congrArg Subtype.val hab
    rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe] at h1
    exact (cancel_mono u.1).mp h1
  refine ⟨NeronModelInfra.schemeHomOverComp τ v, ?_, ?_, ?_⟩
  · rw [NeronModelInfra.schemeHomOverComp_coe]; infer_instance
  · intro χ χ'
    apply hinj
    rw [humul]
    have e1 : ∀ η : torusCoord (ResidueField A) t →ₐ[ResidueField A] ResidueField A,
        NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField A) t η)
            (NeronModelInfra.schemeHomOverComp τ v)) u =
          NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField A) t η) τ := by
      intro η
      apply Subtype.ext
      simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
      rw [hvu, Category.comp_id]
    rw [e1, e1, e1]
    exact hτmul χ χ'
  · rw [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, ← hufst, ← Category.assoc v.1, hvu, Category.id_comp]

end Alpha

theorem solution
    {R₀ : Type u} [CommRing R₀] {A : Type u} [CommRing A] [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (σ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R₀))
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R₀)) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (L : RelativeGroupLaw R₀ g) (hcomm : L.IsCommutative)
    (m : ℕ) (hm : 0 < m) (hqf : LocallyQuasiFinite (L.schemeNsmul m)) (hfl : Flat (L.schemeNsmul m))
    (t : ℕ)
    (τ : SchemeHomOver (torusStr (ResidueField A) t)
      (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (residue A)) ≫ σ) g))
    (hτ : IsClosedImmersion τ.1)
    (hτmul : ∀ χ χ' : WithConv (torusCoord (ResidueField A) t →ₐ[ResidueField A] ResidueField A),
      NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField A) t (χ * χ').ofConv) τ =
        (L.baseChange (Spec.map (CommRingCat.ofHom (residue A)) ≫ σ)).mul _
          (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField A) t χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField A) t χ'.ofConv) τ)) :
    ∃ ι : SchemeHomOver (muStr A t m) (RelativeGroupLaw.baseChangeStr σ g),
      (IsClosedImmersion ι.1 ∧
      (∀ (S : Type u) [CommRing S] [Algebra A S] (χ χ' : WithConv (muCoord A t m →ₐ[A] S)),
        NeronModelInfra.schemeHomOverComp (muPt A S t m (χ * χ').ofConv) ι =
          (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A S t m χ.ofConv) ι)
            (NeronModelInfra.schemeHomOverComp (muPt A S t m χ'.ofConv) ι)) ∧
      (muBaseChange (residue A) t m ≫ ι.1 ≫ pullback.fst g σ =
        muToTorus (ResidueField A) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue A)) ≫ σ))) ∧
      ∀ ι' : SchemeHomOver (muStr A t m) (RelativeGroupLaw.baseChangeStr σ g),
        (∀ (S : Type u) [CommRing S] [Algebra A S] (χ χ' : WithConv (muCoord A t m →ₐ[A] S)),
          NeronModelInfra.schemeHomOverComp (muPt A S t m (χ * χ').ofConv) ι' =
            (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A S t m χ.ofConv) ι')
              (NeronModelInfra.schemeHomOverComp (muPt A S t m χ'.ofConv) ι')) →
        (muBaseChange (residue A) t m ≫ ι'.1 ≫ pullback.fst g σ =
          muToTorus (ResidueField A) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue A)) ≫ σ)) →
        ι' = ι := by

  let res : Spec (CommRingCat.of (ResidueField A)) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (residue A))
  let gA : pullback g σ ⟶ Spec (CommRingCat.of A) := RelativeGroupLaw.baseChangeStr σ g
  let LA : RelativeGroupLaw A gA := L.baseChange σ

  haveI : Smooth gA := by change Smooth (pullback.snd g σ); infer_instance
  haveI : IsSeparated gA := by change IsSeparated (pullback.snd g σ); infer_instance
  haveI : QuasiCompact gA := by change QuasiCompact (pullback.snd g σ); infer_instance
  have hcommA : LA.IsCommutative := RelativeGroupLaw.IsCommutative.baseChange σ hcomm
  have hmap := (GoodReductionJacobian.RelativeGroupLaw.baseChange_schemeNsmul_comp_fst_and_eq_pullback_map σ L m).2.2
  have hqfA : LocallyQuasiFinite (LA.schemeNsmul m) := by
    change LocallyQuasiFinite ((L.baseChange σ).schemeNsmul m)
    rw [hmap]
    exact MorphismProperty.pullback_map (P := @LocallyQuasiFinite) hqf inferInstance (L.schemeNsmul_over m).symm
      (Category.id_comp σ).symm
  have hflA : Flat (LA.schemeNsmul m) := by
    change Flat ((L.baseChange σ).schemeNsmul m)
    rw [hmap]
    exact MorphismProperty.pullback_map (P := @Flat) hfl inferInstance (L.schemeNsmul_over m).symm (Category.id_comp σ).symm

  obtain ⟨τ', hτ', hτ'mul, hreb⟩ := Alpha.exists_transported_torus σ g L t τ hτ hτmul

  obtain ⟨ι, ⟨h1, h2, h3⟩, hU⟩ :=
    AlgebraicGeometry.SplitTorus.existsUnique_muLift_of_torusFibre_of_henselian gA LA hcommA t τ' hτ' hτ'mul m hm hqfA hflA

  have hring : (AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) (residue A)).comp (algebraMap A (muCoord A t m)) =
      ((AddMonoidAlgebra.mapDomainRingHom (ResidueField A)
          (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i))).comp
        (algebraMap (ResidueField A) (torusCoord (ResidueField A) t))).comp (residue A) := by
    refine RingHom.ext (fun a => ?_)
    simp only [RingHom.comp_apply, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self,
      RingHom.id_apply, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, map_zero,
      AddMonoidAlgebra.mapRingHom_single]
  have hsnd : muBaseChange (residue A) t m ≫ muStr A t m =
      muToTorus (ResidueField A) t m ≫ torusStr (ResidueField A) t ≫ res := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun r => Spec.map (CommRingCat.ofHom r)) hring
  refine ⟨ι, ⟨h1, h2, ?_⟩, fun ι' h2' h3' => hU ι' h2' ?_⟩
  ·
    rw [← Category.assoc (muBaseChange (residue A) t m), h3, Category.assoc, Category.assoc, hreb]
  ·
    apply pullback.hom_ext
    · rw [Category.assoc, h3', Category.assoc, Category.assoc, hreb]
    · rw [Category.assoc, Category.assoc, Category.assoc]
      have e1 : ι'.1 ≫ pullback.snd g σ = muStr A t m := ι'.2
      have e2 : pullback.fst gA res ≫ pullback.snd g σ = pullback.snd gA res ≫ res := pullback.condition
      have e3 : τ'.1 ≫ pullback.snd gA res = torusStr (ResidueField A) t := τ'.2
      rw [e1, e2, ← Category.assoc τ'.1, e3]
      exact hsnd

end S_AlgebraicGeometry_SplitTorus_existsUnique_muLift_baseChange_of_torusFibre_of_henselian
end P2MW
export P2MW.S_AlgebraicGeometry_SplitTorus_existsUnique_muLift_baseChange_of_torusFibre_of_henselian (solution)

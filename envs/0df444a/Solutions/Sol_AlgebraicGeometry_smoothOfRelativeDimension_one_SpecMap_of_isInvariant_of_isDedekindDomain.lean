-- Prove2me | solution 1 for AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isDedekindDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a5673210-ba9f-5d0c-87ba-6beb51acc8c1

import Mathlib
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAdicComplete_of_isAlgClosed_residueField
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAlgClosed
import Theorems.Thm_Algebra_TensorProduct_injective_map_fixedPoints_val_and_range_eq_of_flat
import Theorems.Thm_Algebra_IsInvariant_flat_and_finiteType_of_isDedekindDomain
import Theorems.Thm_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isDedekindDomain
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AdicCompletion.map_smul_of AdicCompletion.algebraMap_of AdicCompletion.stabilizer_smul_of AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped TensorProduct

namespace WildRingGC4

section BaseChange

variable {B S A : Type} [CommRing B] [CommRing S] [CommRing A]
  [Algebra B S] [Algebra B A] [Algebra S A] [IsScalarTower B S A]
  (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G B A]
  (T : Type) [CommRing T] [Algebra B T]

@[reducible] noncomputable def tensorAction : MulSemiringAction G (T ⊗[B] A) where
  smul g x := Algebra.TensorProduct.map (AlgHom.id T T) (MulSemiringAction.toAlgHom B A g) x
  one_smul x := by
    change Algebra.TensorProduct.map (AlgHom.id T T) (MulSemiringAction.toAlgHom B A 1) x = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => rw [map_add, hx, hy]
  mul_smul g h x := by
    change Algebra.TensorProduct.map (AlgHom.id T T) (MulSemiringAction.toAlgHom B A (g * h)) x =
      Algebra.TensorProduct.map (AlgHom.id T T) (MulSemiringAction.toAlgHom B A g)
        (Algebra.TensorProduct.map (AlgHom.id T T) (MulSemiringAction.toAlgHom B A h) x)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [mul_smul]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  smul_zero g := map_zero _
  smul_add g x y := map_add _ x y
  smul_one g := map_one _
  smul_mul g x y := map_mul _ x y

@[reducible] noncomputable def tensorAlgebra : Algebra (T ⊗[B] S) (T ⊗[B] A) :=
  (Algebra.TensorProduct.map (AlgHom.id T T) (IsScalarTower.toAlgHom B S A)).toRingHom.toAlgebra

attribute [local instance] tensorAction tensorAlgebra

private theorem _root_.WildRingGC4.smul_def (g : G) (x : T ⊗[B] A) :
    g • x = Algebra.TensorProduct.map (AlgHom.id T T) (MulSemiringAction.toAlgHom B A g) x := rfl

p2m_export "WildRingGC4" "smul_def"
theorem algebraMap_def (s : T ⊗[B] S) :
    algebraMap (T ⊗[B] S) (T ⊗[B] A) s = Algebra.TensorProduct.map (AlgHom.id T T) (IsScalarTower.toAlgHom B S A) s := rfl

theorem isScalarTower_tensor : IsScalarTower T (T ⊗[B] S) (T ⊗[B] A) :=
  IsScalarTower.of_algebraMap_eq fun r =>
    ((Algebra.TensorProduct.map (AlgHom.id T T) (IsScalarTower.toAlgHom B S A)).commutes r).symm

theorem smulCommClass_base : SMulCommClass G T (T ⊗[B] A) :=
  ⟨fun g c x => by rw [smul_def, smul_def, map_smul]⟩

theorem smulCommClass_tensor [SMulCommClass G S A] : SMulCommClass G (T ⊗[B] S) (T ⊗[B] A) := by
  refine ⟨fun g s x => ?_⟩
  have hfix : g • (algebraMap (T ⊗[B] S) (T ⊗[B] A) s) = algebraMap (T ⊗[B] S) (T ⊗[B] A) s := by
    rw [algebraMap_def, smul_def]
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul t s' => simp [smul_algebraMap]
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]

theorem exists_algEquiv_fixedPoints [FaithfulSMul S A] [SMulCommClass G S A] [Algebra.IsInvariant S A G] :
    ∃ e : S ≃ₐ[B] ↥(FixedPoints.subalgebra B A G),
      (FixedPoints.subalgebra B A G).val.comp e.toAlgHom = IsScalarTower.toAlgHom B S A := by
  have hmem : ∀ s : S, IsScalarTower.toAlgHom B S A s ∈ FixedPoints.subalgebra B A G := fun s g => by
    change g • algebraMap S A s = algebraMap S A s
    exact smul_algebraMap g s
  let e₀ : S →ₐ[B] ↥(FixedPoints.subalgebra B A G) := (IsScalarTower.toAlgHom B S A).codRestrict _ hmem
  have hinj : Function.Injective e₀ := fun x y h => FaithfulSMul.algebraMap_injective S A (congrArg Subtype.val h)
  have hsurj : Function.Surjective e₀ := fun a => by
    obtain ⟨s, hs⟩ := Algebra.IsInvariant.isInvariant (A := S) (G := G) a.1 a.2
    exact ⟨s, Subtype.ext hs⟩
  exact ⟨AlgEquiv.ofBijective e₀ ⟨hinj, hsurj⟩, rfl⟩

theorem faithfulSMul_tensor [FaithfulSMul S A] [Module.Flat B T] : FaithfulSMul (T ⊗[B] S) (T ⊗[B] A) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := T) (IsScalarTower.toAlgHom B S A).toLinearMap
    (FaithfulSMul.algebraMap_injective S A)
  intro x y hxy
  exact h hxy

theorem isInvariant_tensor [FaithfulSMul S A] [SMulCommClass G S A] [Algebra.IsInvariant S A G] [Module.Flat B T] :
    Algebra.IsInvariant (T ⊗[B] S) (T ⊗[B] A) G := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨e, he⟩ := exists_algEquiv_fixedPoints (B := B) (S := S) (A := A) G
  have hrange := (Algebra.TensorProduct.injective_map_fixedPoints_val_and_range_eq_of_flat B A T G).2
  have hx' : x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id T T) (FixedPoints.subalgebra B A G).val) := by
    rw [hrange]
    exact fun g => (smul_def G T g x) ▸ hx g
  obtain ⟨y, rfl⟩ := hx'
  obtain ⟨z, rfl⟩ := TensorProduct.map_surjective (g := (LinearMap.id : T →ₗ[B] T)) Function.surjective_id
    (g' := e.toAlgHom.toLinearMap) e.surjective y
  refine ⟨z, ?_⟩
  rw [algebraMap_def]
  clear hx hrange
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t s =>
    simp only [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.id_apply,
      AlgHom.toLinearMap_apply]
    rw [← AlgHom.congr_fun he s]
    rfl
  | add x y hx hy => simp only [map_add]; rw [hx, hy]

omit [SMulCommClass G B A] in
theorem smooth_tensor [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap B A)))] :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap T (T ⊗[B] A)))) := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  have h1 : SmoothOfRelativeDimension 1
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B T)))
        (Spec.map (CommRingCat.ofHom (algebraMap B A)))) :=
    MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension 1) _ _ ‹_›
  rw [← pullbackSpecIso_inv_fst' B T A]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) _ _).mpr h1

end BaseChange

section Fibres

attribute [local instance] tensorAction tensorAlgebra

theorem smooth_geom {B S A : Type} [CommRing B] [CommRing S] [CommRing A]
    [Algebra B S] [Algebra B A] [Algebra S A] [IsScalarTower B S A] [FaithfulSMul S A]
    (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G B A] [SMulCommClass G S A]
    [Algebra.IsInvariant S A G]
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap B A)))]
    (k : Type) [Field k] [IsAlgClosed k] [Algebra B k] [Module.Flat B k] :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k (k ⊗[B] S)))) := by
  haveI := isScalarTower_tensor (B := B) (S := S) (A := A) k
  haveI := smulCommClass_base (B := B) (A := A) G k
  haveI := smulCommClass_tensor (B := B) (S := S) (A := A) G k
  haveI := faithfulSMul_tensor (B := B) (S := S) (A := A) k
  haveI := isInvariant_tensor (B := B) (S := S) (A := A) G k
  haveI := smooth_tensor (B := B) (A := A) k
  exact AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAlgClosed
    (k := k) (S := k ⊗[B] S) (A := k ⊗[B] A) G

theorem smooth_witness {B S A : Type} [CommRing B] [CommRing S] [CommRing A]
    [Algebra B S] [Algebra B A] [Algebra S A] [IsScalarTower B S A] [FaithfulSMul S A]
    (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G B A] [SMulCommClass G S A]
    [Algebra.IsInvariant S A G]
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap B A)))]
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [IsAlgClosed (IsLocalRing.ResidueField W)]
    [Algebra B W] [Module.Flat B W] :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
      (algebraMap (IsLocalRing.ResidueField W) ((IsLocalRing.ResidueField W) ⊗[B] S)))) := by
  haveI := isScalarTower_tensor (B := B) (S := S) (A := A) W
  haveI := smulCommClass_base (B := B) (A := A) G W
  haveI := smulCommClass_tensor (B := B) (S := S) (A := A) G W
  haveI := faithfulSMul_tensor (B := B) (S := S) (A := A) W
  haveI := isInvariant_tensor (B := B) (S := S) (A := A) G W
  haveI := smooth_tensor (B := B) (A := A) W

  haveI hW1 : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap W (W ⊗[B] S)))) :=
    AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAdicComplete_of_isAlgClosed_residueField
      W (S := W ⊗[B] S) (A := W ⊗[B] A) G

  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  have e1 : Spec.map (CommRingCat.ofHom (algebraMap W (IsLocalRing.ResidueField W))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B W)) =
      Spec.map (CommRingCat.ofHom (algebraMap B (IsLocalRing.ResidueField W))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have h3 : SmoothOfRelativeDimension 1 (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B W)))
      (Spec.map (CommRingCat.ofHom (algebraMap B S)))) := by
    have := hW1
    rw [← pullbackSpecIso_inv_fst' B W S] at this
    exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) _ _).mp this
  have h4 : SmoothOfRelativeDimension 1
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap W (IsLocalRing.ResidueField W))))
        (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B W)))
          (Spec.map (CommRingCat.ofHom (algebraMap B S))))) :=
    MorphismProperty.pullback_fst _ _ h3
  have h5 : SmoothOfRelativeDimension 1
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap W (IsLocalRing.ResidueField W))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap B W)))
        (Spec.map (CommRingCat.ofHom (algebraMap B S)))) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1)
      (pullbackRightPullbackFstIso (Spec.map (CommRingCat.ofHom (algebraMap B W)))
        (Spec.map (CommRingCat.ofHom (algebraMap B S)))
        (Spec.map (CommRingCat.ofHom (algebraMap W (IsLocalRing.ResidueField W))))).hom,
      pullbackRightPullbackFstIso_hom_fst]
    exact h4
  have h6 : SmoothOfRelativeDimension 1
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B (IsLocalRing.ResidueField W))))
        (Spec.map (CommRingCat.ofHom (algebraMap B S)))) := by
    have hc : (pullback.congrHom e1 rfl).inv ≫ pullback.fst _ _ =
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B (IsLocalRing.ResidueField W))))
          (Spec.map (CommRingCat.ofHom (algebraMap B S))) := by
      simp only [pullback.congrHom_inv, pullback.lift_fst, Category.comp_id]
    rw [← hc]
    exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) _ _).mpr h5
  rw [← pullbackSpecIso_inv_fst' B (IsLocalRing.ResidueField W) S]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) _ _).mpr h6

end Fibres

end WildRingGC4

open WildRingGC4 in
theorem solution
    {B S A : Type} [CommRing B] [IsDedekindDomain B] [CommRing S] [CommRing A]
    [Algebra B S] [Algebra B A] [Algebra S A] [IsScalarTower B S A] [FaithfulSMul S A]
    (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G B A] [SMulCommClass G S A]
    [Algebra.IsInvariant S A G]
    (hW : ∀ 𝔭 : Ideal B, 𝔭.IsMaximal →
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : IsAlgClosed (IsLocalRing.ResidueField W))
        (_ : Algebra B W), Module.Flat B W ∧ (IsLocalRing.maximalIdeal W).comap (algebraMap B W) = 𝔭)
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap B A)))] :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap B S))) := by
  classical

  have hsmA : Smooth (Spec.map (CommRingCat.ofHom (algebraMap B A))) := SmoothOfRelativeDimension.smooth 1 _
  have hlftA : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap B A))) := inferInstance
  have hflatA : Flat (Spec.map (CommRingCat.ofHom (algebraMap B A))) := inferInstance
  haveI hftA : Algebra.FiniteType B A :=
    RingHom.finiteType_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hlftA)
  haveI hflA : Module.Flat B A :=
    RingHom.flat_algebraMap_iff.mp ((HasRingHomProperty.Spec_iff (P := @Flat)).mp hflatA)
  obtain ⟨hflS, hftS⟩ := Algebra.IsInvariant.flat_and_finiteType_of_isDedekindDomain (B := B) (S := S) (A := A) G
  haveI := hftS
  haveI : Algebra.FinitePresentation B S := (Algebra.FinitePresentation.of_finiteType).mp hftS
  haveI : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap B S))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr ‹_›)
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap B S))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (RingHom.flat_algebraMap_iff.mpr hflS)

  have fibre : ∀ (k : Type) [Field k] [Algebra B k]
      (hsm : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k (k ⊗[B] S)))))
      (y : ↥(Spec (CommRingCat.of S)))
      (hpt : (Spec.map (CommRingCat.ofHom (algebraMap B S))) y =
        (Spec.map (CommRingCat.ofHom (algebraMap B k))) (IsLocalRing.closedPoint k)),
      ∃ U : (Spec (CommRingCat.of S)).Opens,
        y ∈ U ∧ SmoothOfRelativeDimension 1 (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap B S))) := by
    intro k _ _ hsm y hpt
    have hsnd : SmoothOfRelativeDimension 1
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap B S)))
          (Spec.map (CommRingCat.ofHom (algebraMap B k)))) := by
      rw [← pullbackSymmetry_hom_comp_fst,
        MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1)]
      rw [← pullbackSpecIso_inv_fst' B k S] at hsm
      exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) _ _).mp hsm
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Spec.map (CommRingCat.ofHom (algebraMap B S))) (g := Spec.map (CommRingCat.ofHom (algebraMap B k)))
      y (IsLocalRing.closedPoint k) hpt
    exact AlgebraicGeometry.exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd
      (Spec.map (CommRingCat.ofHom (algebraMap B S))) (Spec.map (CommRingCat.ofHom (algebraMap B k)))
      hsnd y ⟨z, hz⟩
  have key : ∀ y : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens,
      y ∈ U ∧ SmoothOfRelativeDimension 1 (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap B S))) := by
    intro y
    let 𝔭 : Ideal B := ((Spec.map (CommRingCat.ofHom (algebraMap B S))) y).asIdeal
    by_cases h𝔭 : 𝔭 = ⊥
    ·
      let k : Type := AlgebraicClosure (FractionRing B)
      haveI : Module.Flat B k := Module.Flat.trans B (FractionRing B) k
      have hinj : Function.Injective (algebraMap B k) := by
        rw [IsScalarTower.algebraMap_eq B (FractionRing B) k]
        exact (algebraMap (FractionRing B) k).injective.comp (IsFractionRing.injective B (FractionRing B))
      refine fibre k (smooth_geom (B := B) (S := S) (A := A) G k) y ?_
      apply PrimeSpectrum.ext
      change 𝔭 = Ideal.comap (algebraMap B k) (IsLocalRing.maximalIdeal k)
      rw [h𝔭, IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
    ·
      have hmax : 𝔭.IsMaximal := Ideal.IsPrime.isMaximal (PrimeSpectrum.isPrime _) h𝔭
      obtain ⟨W, _, _, _, _, _, _, hWfl, hW𝔭⟩ := hW 𝔭 hmax
      haveI := hWfl
      let k := IsLocalRing.ResidueField W
      refine fibre k (smooth_witness (B := B) (S := S) (A := A) G W) y ?_
      apply PrimeSpectrum.ext
      change 𝔭 = Ideal.comap (algebraMap B k) (IsLocalRing.maximalIdeal k)
      rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker, IsScalarTower.algebraMap_eq B W k,
        IsLocalRing.ResidueField.algebraMap_eq, ← RingHom.comap_ker, IsLocalRing.ker_residue, hW𝔭]
  choose U hU using key
  have hsup : iSup U = ⊤ :=
    eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, (hU y).1⟩
  exact (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @SmoothOfRelativeDimension 1) U hsup).mpr
    fun y => (hU y).2

end S_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isDedekindDomain
end P2MW
export P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isDedekindDomain (solution)

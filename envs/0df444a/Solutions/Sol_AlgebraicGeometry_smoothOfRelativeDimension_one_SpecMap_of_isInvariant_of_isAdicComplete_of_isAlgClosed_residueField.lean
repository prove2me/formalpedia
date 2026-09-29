-- Prove2me | solution 1 for AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAdicComplete_of_isAlgClosed_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/26f090bf-7f94-5a1a-8235-a6bbaf38a762

import Mathlib
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd
import Theorems.Thm_Algebra_TensorProduct_injective_map_fixedPoints_val_and_range_eq_of_flat
import Theorems.Thm_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType
import Theorems.Thm_AlgebraicGeometry_exists_adicCompletion_atPrime_ringEquiv_powerSeries_of_isInvariant_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_one_pullback_snd_residueField_of_forall_adicCompletion_atPrime_ringEquiv_powerSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAdicComplete_of_isAlgClosed_residueField
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AdicCompletion.map_smul_of AdicCompletion.algebraMap_of AdicCompletion.stabilizer_smul_of AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

open scoped TensorProduct

namespace WildCoreW21

theorem smoothOfRelativeDimension_one_baseChange'
    {B S A : Type} [CommRing B] [CommRing S] [CommRing A]
    [Algebra B S] [Algebra B A] [Algebra S A] [IsScalarTower B S A]
    (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G B A]
    [SMulCommClass G S A]
    (k : Type) [Field k] [IsAlgClosed k] [Algebra B k]
    (hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id k k) (IsScalarTower.toAlgHom B S A)))
    (hbc : ∀ x : k ⊗[B] A,
      (∀ g : G, Algebra.TensorProduct.map (AlgHom.id k k) (MulSemiringAction.toAlgHom B A g) x = x) ↔
        x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id k k) (IsScalarTower.toAlgHom B S A)))
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap B A)))] :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k (k ⊗[B] S)))) := by
  classical
  let ι : k ⊗[B] S →ₐ[k] k ⊗[B] A :=
    Algebra.TensorProduct.map (AlgHom.id k k) (IsScalarTower.toAlgHom B S A)
  letI algSA : Algebra (k ⊗[B] S) (k ⊗[B] A) := ι.toRingHom.toAlgebra
  have alg_def : ∀ s : k ⊗[B] S, algebraMap (k ⊗[B] S) (k ⊗[B] A) s = ι s := fun _ => rfl
  haveI : IsScalarTower k (k ⊗[B] S) (k ⊗[B] A) :=
    IsScalarTower.of_algebraMap_eq fun r => (ι.commutes r).symm

  letI act : MulSemiringAction G (k ⊗[B] A) :=
    { smul := fun g x =>
        Algebra.TensorProduct.map (AlgHom.id k k) (MulSemiringAction.toAlgHom B A g) x
      one_smul := fun x => by
        change Algebra.TensorProduct.map (AlgHom.id k k) (MulSemiringAction.toAlgHom B A 1) x = x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp
        | add x y hx hy => rw [map_add, hx, hy]
      mul_smul := fun g h x => by
        change Algebra.TensorProduct.map (AlgHom.id k k) (MulSemiringAction.toAlgHom B A (g * h)) x =
          Algebra.TensorProduct.map (AlgHom.id k k) (MulSemiringAction.toAlgHom B A g)
            (Algebra.TensorProduct.map (AlgHom.id k k) (MulSemiringAction.toAlgHom B A h) x)
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [mul_smul]
        | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
      smul_zero := fun g => map_zero _
      smul_add := fun g x y => map_add _ x y
      smul_one := fun g => map_one _
      smul_mul := fun g x y => map_mul _ x y }
  have act_def : ∀ (g : G) (x : k ⊗[B] A),
      g • x = Algebra.TensorProduct.map (AlgHom.id k k) (MulSemiringAction.toAlgHom B A g) x :=
    fun _ _ => rfl
  haveI : SMulCommClass G k (k ⊗[B] A) :=
    ⟨fun g c x => by rw [act_def, act_def, map_smul]⟩
  have hfix : ∀ (g : G) (s : k ⊗[B] S),
      Algebra.TensorProduct.map (AlgHom.id k k) (MulSemiringAction.toAlgHom B A g)
        (algebraMap (k ⊗[B] S) (k ⊗[B] A) s) = algebraMap (k ⊗[B] S) (k ⊗[B] A) s :=
    fun g s => ((hbc (ι s)).mpr ⟨s, rfl⟩) g
  haveI : SMulCommClass G (k ⊗[B] S) (k ⊗[B] A) :=
    ⟨fun g s x => by simp only [Algebra.smul_def, act_def, map_mul, hfix]⟩
  haveI : Algebra.IsInvariant (k ⊗[B] S) (k ⊗[B] A) G :=
    ⟨fun b hb => by
      obtain ⟨a, ha⟩ := (hbc b).mp (fun g => by rw [← act_def]; exact hb g)
      exact ⟨a, ha⟩⟩

  haveI : FaithfulSMul (k ⊗[B] S) (k ⊗[B] A) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact hinj

  haveI : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k (k ⊗[B] A)))) := by
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
    have h1 : SmoothOfRelativeDimension 1
        (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B k)))
          (Spec.map (CommRingCat.ofHom (algebraMap B A)))) :=
      MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension 1) _ _ ‹_›
    rw [← pullbackSpecIso_inv_fst' B k A]
    exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) _ _).mpr h1
  exact AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAlgClosed
    (S := k ⊗[B] S) (A := k ⊗[B] A) G

theorem inj_and_bc_of_flat
    {B S A : Type} [CommRing B] [CommRing S] [CommRing A]
    [Algebra B S] [Algebra B A] [Algebra S A] [IsScalarTower B S A] [FaithfulSMul S A]
    (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G B A] [SMulCommClass G S A]
    [Algebra.IsInvariant S A G]
    (k : Type) [CommRing k] [Algebra B k] [Module.Flat B k] :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id k k) (IsScalarTower.toAlgHom B S A)) ∧
    ∀ x : k ⊗[B] A,
      (∀ g : G, Algebra.TensorProduct.map (AlgHom.id k k) (MulSemiringAction.toAlgHom B A g) x = x) ↔
        x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id k k) (IsScalarTower.toAlgHom B S A)) := by
  classical
  let F := FixedPoints.subalgebra B A G
  let φ : S →ₐ[B] A := IsScalarTower.toAlgHom B S A
  have hmem : ∀ s : S, φ s ∈ F := fun s g => smul_algebraMap g s
  have hsurj : ∀ a ∈ F, ∃ s : S, φ s = a := fun a ha => Algebra.IsInvariant.isInvariant (A := S) a ha
  let ψ₀ : S →ₐ[B] F := φ.codRestrict F hmem
  have hψ₀ : Function.Bijective ψ₀ := by
    constructor
    · intro s t h
      apply FaithfulSMul.algebraMap_injective S A
      exact congrArg Subtype.val h
    · rintro ⟨a, ha⟩
      obtain ⟨s, hs⟩ := hsurj a ha
      exact ⟨s, Subtype.ext hs⟩
  let ψ : S ≃ₐ[B] F := AlgEquiv.ofBijective ψ₀ hψ₀
  have hφ : φ = F.val.comp (ψ : S →ₐ[B] F) := by ext s; rfl
  have hmapφ : Algebra.TensorProduct.map (AlgHom.id k k) φ =
      (Algebra.TensorProduct.map (AlgHom.id k k) F.val).comp
        (Algebra.TensorProduct.map (AlgHom.id k k) (ψ : S →ₐ[B] F)) := by
    rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp, ← hφ]
  have hψbij : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id k k) (ψ : S →ₐ[B] F)) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) ψ).bijective
  obtain ⟨hinj, hrange⟩ := Algebra.TensorProduct.injective_map_fixedPoints_val_and_range_eq_of_flat B A k G
  refine ⟨?_, fun x => ?_⟩
  · show Function.Injective (Algebra.TensorProduct.map (AlgHom.id k k) φ)
    rw [hmapφ]; exact hinj.comp hψbij.1
  · show _ ↔ x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id k k) φ)
    have hr : Set.range (Algebra.TensorProduct.map (AlgHom.id k k) φ) =
        Set.range (Algebra.TensorProduct.map (AlgHom.id k k) F.val) := by
      rw [hmapφ, AlgHom.coe_comp, hψbij.2.range_comp]
    rw [hr, hrange]
    exact Iff.rfl

end WildCoreW21

open WildCoreW21 in
theorem solution
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    [IsAlgClosed (ResidueField W)]
    {S A : Type} [CommRing S] [CommRing A]
    [Algebra W S] [Algebra W A] [Algebra S A] [IsScalarTower W S A] [FaithfulSMul S A]
    (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G W A] [SMulCommClass G S A]
    [Algebra.IsInvariant S A G]
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap W A)))] :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap W S))) := by
  classical
  set f := Spec.map (CommRingCat.ofHom (algebraMap W S)) with hf

  have hsmA : Smooth (Spec.map (CommRingCat.ofHom (algebraMap W A))) := SmoothOfRelativeDimension.smooth 1 _
  have hlftA : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap W A))) := inferInstance
  have hflatA : Flat (Spec.map (CommRingCat.ofHom (algebraMap W A))) := inferInstance
  haveI hftA : Algebra.FiniteType W A :=
    RingHom.finiteType_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hlftA)
  have hflA : Module.Flat W A :=
    RingHom.flat_algebraMap_iff.mp ((HasRingHomProperty.Spec_iff (P := @Flat)).mp hflatA)

  obtain ⟨-, hftS⟩ := Algebra.IsInvariant.moduleFinite_and_finiteType_of_finiteType W S A G
  haveI := hftS
  have hflS : Module.Flat W S := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot] at hflA
    intro s hs
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff s).1 hs
    have h3 : algebraMap S A ((a : W) • s) = (a : W) • algebraMap S A s :=
      map_smul (IsScalarTower.toAlgHom W S A) (a : W) s
    have h1 : algebraMap S A s ∈ Submodule.torsion W A := by
      refine (Submodule.mem_torsion_iff _).2 ⟨a, ?_⟩
      rw [Submonoid.smul_def] at ha ⊢
      rw [← h3, ha, map_zero]
    rw [hflA] at h1
    have h2 : algebraMap S A s = 0 := h1
    exact (FaithfulSMul.algebraMap_injective S A) (by rw [h2, map_zero])
  haveI : Algebra.FinitePresentation W S := (Algebra.FinitePresentation.of_finiteType).mp hftS
  haveI : LocallyOfFinitePresentation f :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr ‹_›)
  haveI : Flat f := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (RingHom.flat_algebraMap_iff.mpr hflS)

  have key : ∀ y : ↥(Spec (CommRingCat.of S)), ∃ V : (Spec (CommRingCat.of S)).Opens,
      y ∈ V ∧ SmoothOfRelativeDimension 1 (V.ι ≫ f) := by
    intro y
    let 𝔭 : Ideal W := (f.base y).asIdeal
    by_cases h𝔭 : 𝔭 = maximalIdeal W
    ·
      have hsnd : SmoothOfRelativeDimension 1
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap W (ResidueField W))))) :=
        AlgebraicGeometry.smoothOfRelativeDimension_one_pullback_snd_residueField_of_forall_adicCompletion_atPrime_ringEquiv_powerSeries
          W (S := S) (fun 𝔮 _ _ =>
            AlgebraicGeometry.exists_adicCompletion_atPrime_ringEquiv_powerSeries_of_isInvariant_of_smoothOfRelativeDimension_one
              W (S := S) (A := A) G 𝔮)
      have hpt : f.base y = (Spec.map (CommRingCat.ofHom (algebraMap W (ResidueField W)))).base
          (closedPoint (ResidueField W)) := by
        have h2 : (Spec.map (CommRingCat.ofHom (algebraMap W (ResidueField W)))).base (closedPoint (ResidueField W)) =
            closedPoint W := IsLocalRing.comap_closedPoint (IsLocalRing.residue W)
        rw [h2]
        exact PrimeSpectrum.ext h𝔭
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f)
        (g := Spec.map (CommRingCat.ofHom (algebraMap W (ResidueField W)))) y (closedPoint (ResidueField W)) hpt
      exact AlgebraicGeometry.exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd
        f (Spec.map (CommRingCat.ofHom (algebraMap W (ResidueField W)))) hsnd y ⟨z, hz⟩
    ·
      have h𝔭bot : 𝔭 = ⊥ := by
        by_contra hne
        exact h𝔭 (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne (f.base y).isPrime))
      let k : Type := AlgebraicClosure 𝔭.ResidueField
      have hker : RingHom.ker (algebraMap W k) = ⊥ := by
        rw [IsScalarTower.algebraMap_eq W 𝔭.ResidueField k, ← RingHom.comap_ker,
          (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap 𝔭.ResidueField k).injective, ← RingHom.ker,
          Ideal.ker_algebraMap_residueField]
        exact h𝔭bot
      have hinjk : Function.Injective (algebraMap W k) := (RingHom.injective_iff_ker_eq_bot _).2 hker
      haveI : Module.Flat W k := by
        rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
        intro x hx
        obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).1 hx
        rw [Submonoid.smul_def, Algebra.smul_def] at ha
        have ha0 : algebraMap W k (a : W) ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero a (hinjk (by rw [h, map_zero]))
        exact (mul_eq_zero.1 ha).resolve_left ha0
      obtain ⟨hinj, hbc⟩ := inj_and_bc_of_flat (B := W) (S := S) (A := A) G k
      have hsm := smoothOfRelativeDimension_one_baseChange' (B := W) G k hinj hbc
      have hsnd : SmoothOfRelativeDimension 1
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap W k)))) := by
        rw [← pullbackSymmetry_hom_comp_fst,
          MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1)]
        rw [← pullbackSpecIso_inv_fst' W k S] at hsm
        exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) _ _).mp hsm
      have hpt : f.base y = (Spec.map (CommRingCat.ofHom (algebraMap W k))).base (closedPoint k) := by
        apply PrimeSpectrum.ext
        change 𝔭 = Ideal.comap (algebraMap W k) (maximalIdeal k)
        rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker, hker]
        exact h𝔭bot
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f)
        (g := Spec.map (CommRingCat.ofHom (algebraMap W k))) y (closedPoint k) hpt
      exact AlgebraicGeometry.exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd
        f (Spec.map (CommRingCat.ofHom (algebraMap W k))) hsnd y ⟨z, hz⟩

  choose V hV using key
  have hsup : iSup V = ⊤ :=
    eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, (hV y).1⟩
  exact (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @SmoothOfRelativeDimension 1) V hsup).mpr
    fun y => (hV y).2

end S_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAdicComplete_of_isAlgClosed_residueField
end P2MW
export P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAdicComplete_of_isAlgClosed_residueField (solution)

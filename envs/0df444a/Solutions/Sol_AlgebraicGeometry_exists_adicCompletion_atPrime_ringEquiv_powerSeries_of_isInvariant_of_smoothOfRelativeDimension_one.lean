-- Prove2me | solution 1 for AlgebraicGeometry.exists_adicCompletion_atPrime_ringEquiv_powerSeries_of_isInvariant_of_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/32bd0212-2f97-5f5a-9061-1438206cd12f

import Mathlib
import Definitions.Def_AdicCompletionGaloisAction
import Definitions.Def_InvariantBaseChange
import Theorems.Thm_Algebra_IsInvariant_isInvariant_adicCompletion_stabilizer_and_injective_and_finite
import Theorems.Thm_AlgebraicGeometry_exists_adicCompletion_stalk_ringEquiv_powerSeries_of_smoothOfRelativeDimension_one
import Theorems.Thm_PowerSeries_nonempty_algEquiv_of_forall_mem_iff_forall_apply_eq
import Theorems.Thm_AdicCompletion_exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal
import Theorems.Thm_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_adicCompletion_atPrime_ringEquiv_powerSeries_of_isInvariant_of_smoothOfRelativeDimension_one
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped Pointwise TensorProduct
open scoped AdicCompletion.GaloisAction

namespace LocalForm21

theorem stalk_compat {W A : Type} [CommRing W] [CommRing A] [Algebra W A]
    (x : ↥(Spec (CommRingCat.of A))) (w : W) :
    letI : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk x) := StructureSheaf.stalkAlgebra A x
    ((Spec (CommRingCat.of A)).presheaf.germ ⊤ x trivial).hom
        ((Spec.map (CommRingCat.ofHom (algebraMap W A))).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom w)) =
      algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk x) (algebraMap W A w) := by
  letI : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk x) := StructureSheaf.stalkAlgebra A x
  have h1 : (Spec.map (CommRingCat.ofHom (algebraMap W A))).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom w) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (algebraMap W A w) := by
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap W A))
    have h := congrArg (fun k => k.hom w) this
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h.symm
  rw [h1]
  rfl

theorem glue
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    {Ohat Chat : Type} [CommRing Ohat] [CommRing Chat] (ι : Ohat →+* Chat) (hι : Function.Injective ι)
    (D : Type) [Group D] [Finite D] [MulSemiringAction D Chat]
    (hfix : ∀ (d : D) (x : Ohat), d • ι x = ι x)
    (hinv : ∀ y : Chat, (∀ d : D, d • y = y) → ∃ x : Ohat, ι x = y)
    (Φ : Chat ≃+* PowerSeries W) (jW : W →+* Ohat) (hΦ : ∀ w : W, Φ (ι (jW w)) = PowerSeries.C w) :
    ∃ e : Ohat ≃+* PowerSeries W, ∀ w : W, e (jW w) = PowerSeries.C w := by
  classical
  have hC : ∀ (d : D) (w : W), Φ (d • Φ.symm (PowerSeries.C w)) = PowerSeries.C w := by
    intro d w
    rw [← hΦ w, RingEquiv.symm_apply_apply, hfix]

  let σr : D → (PowerSeries W ≃+* PowerSeries W) := fun d =>
    (Φ.symm.trans (MulSemiringAction.toRingEquiv D Chat d)).trans Φ
  have σr_apply : ∀ (d : D) (f : PowerSeries W), σr d f = Φ (d • Φ.symm f) := fun _ _ => rfl
  let σa : D → (PowerSeries W ≃ₐ[W] PowerSeries W) := fun d =>
    AlgEquiv.ofRingEquiv (f := σr d) (fun w => by
      rw [σr_apply, ← PowerSeries.C_eq_algebraMap]
      exact hC d w)
  have σa_apply : ∀ (d : D) (f : PowerSeries W), σa d f = Φ (d • Φ.symm f) := fun _ _ => rfl
  let σ : D →* (PowerSeries W ≃ₐ[W] PowerSeries W) :=
    { toFun := σa
      map_one' := by
        ext f
        rw [σa_apply, one_smul, RingEquiv.apply_symm_apply, AlgEquiv.one_apply]
      map_mul' := fun d₁ d₂ => by
        ext f
        rw [AlgEquiv.mul_apply, σa_apply, σa_apply, σa_apply, RingEquiv.symm_apply_apply, mul_smul] }
  have σ_apply : ∀ (d : D) (f : PowerSeries W), σ d f = Φ (d • Φ.symm f) := fun _ _ => rfl
  let S' : Subalgebra W (PowerSeries W) :=
    { carrier := {f | ∀ d : D, σ d f = f}
      mul_mem' := fun {a b} ha hb d => by rw [map_mul, ha d, hb d]
      add_mem' := fun {a b} ha hb d => by rw [map_add, ha d, hb d]
      algebraMap_mem' := fun w d => AlgEquiv.commutes (σ d) w }
  have hS' : ∀ f : PowerSeries W, f ∈ S' ↔ ∀ d : D, σ d f = f := fun f => Iff.rfl
  obtain ⟨ψ⟩ := PowerSeries.nonempty_algEquiv_of_forall_mem_iff_forall_apply_eq W D σ S' hS'

  let θ : Ohat →+* PowerSeries W := Φ.toRingHom.comp ι
  have θ_apply : ∀ x : Ohat, θ x = Φ (ι x) := fun _ => rfl
  have hθmem : ∀ x : Ohat, θ x ∈ S' := by
    intro x
    rw [hS']
    intro d
    rw [θ_apply, σ_apply, RingEquiv.symm_apply_apply, hfix]
  have hθinj : Function.Injective (θ.codRestrict S' hθmem) := by
    intro x y h
    have h' : θ x = θ y := congrArg Subtype.val h
    rw [θ_apply, θ_apply] at h'
    exact hι (Φ.injective h')
  have hθsurj : Function.Surjective (θ.codRestrict S' hθmem) := by
    rintro ⟨f, hf⟩
    have hy : ∀ d : D, d • Φ.symm f = Φ.symm f := by
      intro d
      apply Φ.injective
      rw [RingEquiv.apply_symm_apply, ← σ_apply]
      exact (hS' f).mp hf d
    obtain ⟨x, hx⟩ := hinv (Φ.symm f) hy
    refine ⟨x, Subtype.ext ?_⟩
    show θ x = f
    rw [θ_apply, hx, RingEquiv.apply_symm_apply]
  let e₁ : Ohat ≃+* ↥S' := RingEquiv.ofBijective (θ.codRestrict S' hθmem) ⟨hθinj, hθsurj⟩
  have e₁_apply : ∀ x : Ohat, ((e₁ x : ↥S') : PowerSeries W) = Φ (ι x) := fun _ => rfl
  refine ⟨e₁.trans ψ.symm.toRingEquiv, fun w => ?_⟩
  have h1 : e₁ (jW w) = algebraMap W ↥S' w := by
    apply Subtype.ext
    rw [e₁_apply, Subalgebra.coe_algebraMap, hΦ, PowerSeries.C_eq_algebraMap]
  rw [RingEquiv.trans_apply, h1]
  show ψ.symm (algebraMap W ↥S' w) = PowerSeries.C w
  rw [AlgEquiv.commutes, ← PowerSeries.C_eq_algebraMap]

theorem core
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] [IsAlgClosed (ResidueField W)]
    {S A : Type} [CommRing S] [CommRing A] [Algebra W S] [Algebra W A] [Algebra S A] [IsScalarTower W S A]
    [FaithfulSMul S A]
    (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G W A] [SMulCommClass G S A]
    [Algebra.IsInvariant S A G]
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap W A)))]
    (𝔮 : Ideal S) [𝔮.IsMaximal] [𝔮.LiesOver (maximalIdeal W)]
    (O : Type) [CommRing O] [Algebra S O] [IsLocalization.AtPrime O 𝔮] [IsLocalRing O] :
    ∃ e : AdicCompletion (maximalIdeal O) O ≃+* PowerSeries W,
      ∀ a : W, e (algebraMap O _ (algebraMap S O (algebraMap W S a))) = PowerSeries.C a := by
  classical

  have hsmA : Smooth (Spec.map (CommRingCat.ofHom (algebraMap W A))) := SmoothOfRelativeDimension.smooth 1 _
  have hlftA : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap W A))) := inferInstance
  haveI hftA : Algebra.FiniteType W A :=
    RingHom.finiteType_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hlftA)
  obtain ⟨hfinSA, hftS⟩ := Algebra.IsInvariant.moduleFinite_and_finiteType_of_finiteType W S A G
  haveI := hfinSA
  haveI := hftS
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing W S
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing 𝔮.primeCompl O inferInstance
  haveI : Module.Flat S O := IsLocalization.flat O 𝔮.primeCompl

  letI act : MulSemiringAction G (O ⊗[S] A) := Algebra.TensorProduct.rightMulSemiringAction S O A G
  haveI : SMulCommClass G O (O ⊗[S] A) := Algebra.TensorProduct.rightMulSemiringAction_smulCommClass S O A G
  haveI : Algebra.IsInvariant O (O ⊗[S] A) G := Algebra.IsInvariant.isInvariant_tensorProduct_of_flat S O A G
  haveI : Module.Finite O (O ⊗[S] A) := inferInstance
  have hinjOC : Function.Injective (algebraMap O (O ⊗[S] A)) :=
    Algebra.TensorProduct.includeLeft_injective (S := O)
      ((faithfulSMul_iff_algebraMap_injective S A).mp inferInstance)
  haveI : FaithfulSMul O (O ⊗[S] A) := (faithfulSMul_iff_algebraMap_injective O (O ⊗[S] A)).mpr hinjOC

  haveI : Algebra.IsIntegral O (O ⊗[S] A) := inferInstance
  obtain ⟨𝔫, h𝔫max, h𝔫comap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := O ⊗[S] A) (maximalIdeal O)
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinjOC]; exact bot_le)
  haveI := h𝔫max
  haveI : 𝔫.LiesOver (maximalIdeal O) := ⟨h𝔫comap.symm⟩

  obtain ⟨hinvC, hinjC, -, -⟩ :=
    Algebra.IsInvariant.isInvariant_adicCompletion_stabilizer_and_injective_and_finite
      (O := O) (C := O ⊗[S] A) (G := G) 𝔫

  obtain ⟨Φ, hΦ⟩ : ∃ Φ : AdicCompletion 𝔫 (O ⊗[S] A) ≃+* PowerSeries W,
      ∀ w : W, Φ (algebraMap (O ⊗[S] A) _ (algebraMap O (O ⊗[S] A) (algebraMap S O (algebraMap W S w)))) =
        PowerSeries.C w := by

    letI algAC : Algebra A (O ⊗[S] A) := Algebra.TensorProduct.rightAlgebra
    haveI : IsLocalization (Algebra.algebraMapSubmonoid A 𝔮.primeCompl) (O ⊗[S] A) :=
      IsLocalization.tensorRight _ _
    haveI : IsScalarTower A (O ⊗[S] A) (Localization.AtPrime 𝔫) := IsScalarTower.of_algebraMap_eq' rfl
    haveI h𝔫'loc : IsLocalization.AtPrime (Localization.AtPrime 𝔫) (𝔫.comap (algebraMap A (O ⊗[S] A))) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Algebra.algebraMapSubmonoid A 𝔮.primeCompl)
        (Localization.AtPrime 𝔫) 𝔫

    have h𝔫'S : (𝔫.comap (algebraMap A (O ⊗[S] A))).comap (algebraMap S A) = 𝔮 := by
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq S A (O ⊗[S] A),
        IsScalarTower.algebraMap_eq S O (O ⊗[S] A), ← Ideal.comap_comap, h𝔫comap]
      exact IsLocalization.AtPrime.under_maximalIdeal O 𝔮
    haveI h𝔫'max : (𝔫.comap (algebraMap A (O ⊗[S] A))).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := S) _ (by rw [h𝔫'S]; infer_instance)

    let x : ↥(Spec (CommRingCat.of A)) := ⟨𝔫.comap (algebraMap A (O ⊗[S] A)), h𝔫'max.isPrime⟩
    letI algAstk : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk x) := StructureSheaf.stalkAlgebra A x
    haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of A)).presheaf.stalk x)
        (𝔫.comap (algebraMap A (O ⊗[S] A))) :=
      StructureSheaf.IsLocalization.to_stalk A x
    have hx : (Spec.map (CommRingCat.ofHom (algebraMap W A))).base x = closedPoint W := by
      apply PrimeSpectrum.ext
      change (𝔫.comap (algebraMap A (O ⊗[S] A))).comap (algebraMap W A) = maximalIdeal W
      rw [IsScalarTower.algebraMap_eq W S A, ← Ideal.comap_comap, h𝔫'S]
      exact (Ideal.LiesOver.over (p := maximalIdeal W) (P := 𝔮)).symm
    have hxc : IsClosed ({x} : Set ↥(Spec (CommRingCat.of A))) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mpr h𝔫'max
    obtain ⟨e₀, he₀⟩ :=
      AlgebraicGeometry.exists_adicCompletion_stalk_ringEquiv_powerSeries_of_smoothOfRelativeDimension_one W
        (Spec.map (CommRingCat.ofHom (algebraMap W A))) x hx hxc

    obtain ⟨T₁, hT₁⟩ := AdicCompletion.exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal
      (B := A) (S := (Spec (CommRingCat.of A)).presheaf.stalk x) (𝔫.comap (algebraMap A (O ⊗[S] A)))
    obtain ⟨T₂, hT₂⟩ := AdicCompletion.exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal
      (B := A) (S := Localization.AtPrime 𝔫) (𝔫.comap (algebraMap A (O ⊗[S] A)))
    obtain ⟨T₃, hT₃⟩ := AdicCompletion.exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal
      (B := O ⊗[S] A) (S := Localization.AtPrime 𝔫) 𝔫
    refine ⟨T₃.trans (T₂.symm.trans (T₁.trans e₀)), fun w => ?_⟩
    have hOC : algebraMap O (O ⊗[S] A) (algebraMap S O (algebraMap W S w)) =
        algebraMap A (O ⊗[S] A) (algebraMap W A w) := by
      rw [← IsScalarTower.algebraMap_apply S O (O ⊗[S] A), IsScalarTower.algebraMap_apply W S A,
        ← IsScalarTower.algebraMap_apply S A (O ⊗[S] A)]
    rw [hOC, RingEquiv.trans_apply, hT₃, RingEquiv.trans_apply,
      ← IsScalarTower.algebraMap_apply A (O ⊗[S] A) (Localization.AtPrime 𝔫), ← hT₂,
      RingEquiv.symm_apply_apply, RingEquiv.trans_apply, hT₁, ← stalk_compat x w]
    exact he₀ w

  have hjW : ∀ w : W, Φ (algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 (O ⊗[S] A))
      (algebraMap O _ (algebraMap S O (algebraMap W S w)))) = PowerSeries.C w := by
    intro w
    rw [← IsScalarTower.algebraMap_apply O (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 (O ⊗[S] A)),
      IsScalarTower.algebraMap_apply O (O ⊗[S] A) (AdicCompletion 𝔫 (O ⊗[S] A))]
    exact hΦ w
  exact glue W (algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 (O ⊗[S] A))) hinjC
    (MulAction.stabilizer G 𝔫) (fun d y => AdicCompletion.stabilizer_smul_algebraMap _ _ d y)
    (fun y hy => hinvC.isInvariant y hy) Φ
    ((algebraMap O (AdicCompletion (maximalIdeal O) O)).comp ((algebraMap S O).comp (algebraMap W S))) hjW

end LocalForm21

theorem solution
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] [IsAlgClosed (ResidueField W)]
    {S A : Type} [CommRing S] [CommRing A] [Algebra W S] [Algebra W A] [Algebra S A] [IsScalarTower W S A]
    [FaithfulSMul S A]
    (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G W A] [SMulCommClass G S A]
    [Algebra.IsInvariant S A G]
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap W A)))]
    (𝔮 : Ideal S) [𝔮.IsMaximal] [𝔮.LiesOver (maximalIdeal W)] :
    ∃ e : AdicCompletion (maximalIdeal (Localization.AtPrime 𝔮)) (Localization.AtPrime 𝔮) ≃+* PowerSeries W,
      ∀ a : W, e (algebraMap (Localization.AtPrime 𝔮) _
          (algebraMap S (Localization.AtPrime 𝔮) (algebraMap W S a))) = PowerSeries.C a := by
  exact LocalForm21.core W (S := S) (A := A) G 𝔮 (Localization.AtPrime 𝔮)

end S_AlgebraicGeometry_exists_adicCompletion_atPrime_ringEquiv_powerSeries_of_isInvariant_of_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicGeometry_exists_adicCompletion_atPrime_ringEquiv_powerSeries_of_isInvariant_of_smoothOfRelativeDimension_one (solution)

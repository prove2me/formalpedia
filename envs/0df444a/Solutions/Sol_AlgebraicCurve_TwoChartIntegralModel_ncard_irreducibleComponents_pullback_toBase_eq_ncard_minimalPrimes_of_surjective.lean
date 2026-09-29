-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.ncard_irreducibleComponents_pullback_toBase_eq_ncard_minimalPrimes_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a5ca2dab-a08a-591e-baa0-f7b4edee2b8b

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_iotaInf_mem_range_iotaFin_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_ncard_irreducibleComponents_pullback_toBase_eq_ncard_minimalPrimes_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

namespace FibreComp

section Top
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem closure_image_mem_irreducibleComponents {f : Y → X} (hf : Topology.IsOpenEmbedding f)
    {W : Set Y} (hW : W ∈ irreducibleComponents Y) : closure (f '' W) ∈ irreducibleComponents X := by
  refine ⟨(hW.1.image f hf.continuous.continuousOn).closure, fun T hT hle => ?_⟩

  have hne : (T ∩ Set.range f).Nonempty := by
    obtain ⟨y, hy⟩ := hW.1.1
    exact ⟨f y, hle (subset_closure ⟨y, hy, rfl⟩), y, rfl⟩
  have hpre : IsIrreducible (f ⁻¹' T) := hT.preimage hf hne
  have hWle : W ⊆ f ⁻¹' T := fun y hy => hle (subset_closure ⟨y, hy, rfl⟩)
  have hWeq : f ⁻¹' T ⊆ W := hW.2 hpre hWle
  calc T ⊆ closure (T ∩ Set.range f) := subset_closure_inter_of_isPreirreducible_of_isOpen hT.2 hf.isOpen_range hne
    _ = closure (f '' (f ⁻¹' T)) := by rw [Set.image_preimage_eq_inter_range]
    _ ⊆ closure (f '' W) := closure_mono (Set.image_mono hWeq)

theorem ncard_irreducibleComponents_eq_of_isOpenEmbedding {f : Y → X} (hf : Topology.IsOpenEmbedding f)
    (hmeet : ∀ Z ∈ irreducibleComponents X, (Z ∩ Set.range f).Nonempty) :
    (irreducibleComponents X).ncard = (irreducibleComponents Y).ncard := by
  refine Set.ncard_congr (fun Z _ => f ⁻¹' Z) (fun Z hZ => preimage_mem_irreducibleComponents hZ hf (hmeet Z hZ)) ?_ ?_
  · intro Z₁ Z₂ h₁ h₂ heq
    have e₁ := closure_image_preimage_of_isPreirreducible f hf.isOpenMap Z₁ ?_ h₁.1.2 (isClosed_of_mem_irreducibleComponents _ h₁)
    have e₂ := closure_image_preimage_of_isPreirreducible f hf.isOpenMap Z₂ ?_ h₂.1.2 (isClosed_of_mem_irreducibleComponents _ h₂)
    · rw [← e₁, ← e₂, heq]
    · obtain ⟨-, hx, y, rfl⟩ := hmeet Z₂ h₂; exact ⟨y, hx⟩
    · obtain ⟨-, hx, y, rfl⟩ := hmeet Z₁ h₁; exact ⟨y, hx⟩
  · intro W hW
    refine ⟨closure (f '' W), closure_image_mem_irreducibleComponents hf hW, ?_⟩
    show f ⁻¹' closure (f '' W) = W
    rw [← hf.isEmbedding.closure_eq_preimage_closure_image W]
    exact (isClosed_of_mem_irreducibleComponents _ hW).closure_eq

theorem ncard_irreducibleComponents_eq_of_homeomorph (e : X ≃ₜ Y) :
    (irreducibleComponents X).ncard = (irreducibleComponents Y).ncard := by
  refine (ncard_irreducibleComponents_eq_of_isOpenEmbedding e.symm.isOpenEmbedding fun Z hZ => ?_)
  rw [e.symm.range_coe, Set.inter_univ]
  exact hZ.1.1

end Top

section Alg

theorem ncard_irreducibleComponents_primeSpectrum (T : Type*) [CommRing T] :
    (irreducibleComponents (PrimeSpectrum T)).ncard = (minimalPrimes T).ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact (Nat.card_congr (minimalPrimes.equivIrreducibleComponents T).toEquiv).symm

theorem ncard_minimalPrimes_eq_of_surjective {A T : Type*} [CommRing A] [CommRing T] (π : A →+* T)
    (hπ : Function.Surjective π) (I : Ideal A) (hI : RingHom.ker π = I) :
    (minimalPrimes T).ncard = I.minimalPrimes.ncard := by
  have h : I.minimalPrimes = Ideal.comap π '' minimalPrimes T := by
    rw [← hI, RingHom.ker_eq_comap_bot, Ideal.comap_minimalPrimes_eq_of_surjective hπ]
  rw [h, Set.ncard_image_of_injective _ (Ideal.comap_injective_of_surjective π hπ)]

end Alg

end FibreComp

namespace FibreComp

open TensorProduct

section L4
variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  (ϖ : R) (κ : Type u) [Field κ] [Algebra R κ]

private theorem _root_.FibreComp.includeLeft_surjective (hsurj : Function.Surjective (algebraMap R κ)) :
    Function.Surjective (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := κ)) :=
  Algebra.TensorProduct.includeLeft_surjective (R := R) (S := R) (A := A) (T := κ) hsurj

p2m_export "FibreComp" "includeLeft_surjective"
set_option maxHeartbeats 3200000 in
theorem ker_includeLeft (hsurj : Function.Surjective (algebraMap R κ)) (hker : RingHom.ker (algebraMap R κ) = Ideal.span {ϖ}) :
    RingHom.ker (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := κ)) = Ideal.span {algebraMap R A ϖ} := by
  set J : Ideal A := Ideal.span {algebraMap R A ϖ} with hJ
  apply le_antisymm
  ·
    have hle : RingHom.ker (algebraMap R κ) ≤ RingHom.ker (algebraMap R (A ⧸ J)) := by
      rw [hker, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
        IsScalarTower.algebraMap_apply R A (A ⧸ J), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    let g₀ : κ →+* A ⧸ J := RingHom.liftOfSurjective (algebraMap R κ) hsurj ⟨algebraMap R (A ⧸ J), hle⟩
    have hg₀ : ∀ r : R, g₀ (algebraMap R κ r) = algebraMap R (A ⧸ J) r := fun r =>
      RingHom.liftOfSurjective_comp_apply (algebraMap R κ) hsurj ⟨algebraMap R (A ⧸ J), hle⟩ r
    let Φ : A ⊗[R] κ →ₗ[R] A ⧸ J := TensorProduct.lift
      (LinearMap.mk₂ R (fun (a : A) (c : κ) => g₀ c * Ideal.Quotient.mk J a)
        (fun a a' c => by simp [mul_add]) (fun r a c => by
          obtain ⟨s, rfl⟩ := hsurj c
          simp [Algebra.smul_def, hg₀, mul_left_comm])
        (fun a c c' => by simp [add_mul]) (fun r a c => by
          obtain ⟨s, rfl⟩ := hsurj c
          simp only [Algebra.smul_def, ← map_mul, hg₀]
          rw [map_mul, mul_assoc]))
    have hΦ : ∀ a : A, Φ (a ⊗ₜ[R] (1 : κ)) = Ideal.Quotient.mk J a := by
      intro a
      simp [Φ, TensorProduct.lift.tmul]
    intro a ha
    rw [RingHom.mem_ker] at ha
    change a ⊗ₜ[R] (1 : κ) = 0 at ha
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hΦ, ha, map_zero]
  · rw [hJ, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    change algebraMap R A ϖ ⊗ₜ[R] (1 : κ) = 0
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
      show algebraMap R κ ϖ = 0 from by rw [← RingHom.mem_ker, hker]; exact Ideal.subset_span rfl,
      TensorProduct.tmul_zero]

end L4

end FibreComp

namespace FibreComp

open TensorProduct

section Chart

set_option maxHeartbeats 6400000 in
theorem chart {R : Type u} [CommRing R] (κ : Type u) [Field κ] [Algebra R κ]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (A : Type u) [CommRing A] [Algebra R A] (fA : Spec (CommRingCat.of A) ⟶ X)
    (hfA : fA ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (ιA : pullback (fA ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (h1 : ιA ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R κ))) = pullback.fst _ _ ≫ fA) :
    ∃ e : Spec (CommRingCat.of (A ⊗[R] κ)) ≅ pullback (fA ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R κ))),
      (e.hom ≫ ιA) ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R κ))) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := κ))) ≫ fA := by
  let ec : pullback (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) ≅
      pullback (fA ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) :=
    pullback.congrHom hfA.symm rfl
  let eT : Spec (CommRingCat.of (A ⊗[R] κ)) ≅ pullback (fA ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) :=
    (pullbackSpecIso R A κ).symm ≪≫ ec
  refine ⟨eT, ?_⟩
  rw [Category.assoc, h1]
  simp only [eT, ec, Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc]
  erw [pullback.lift_fst_assoc]
  simp only [Category.comp_id]
  erw [pullbackSpecIso_inv_fst_assoc]

end Chart

end FibreComp

open scoped TensorProduct in
open FibreComp in
set_option maxHeartbeats 6400000 in
theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (ϖ : R) (κ : Type u) [Field κ] [Algebra R κ]
    (hsurj : Function.Surjective (algebraMap R κ)) (hker : RingHom.ker (algebraMap R κ) = Ideal.span {ϖ})
    (hInf : ∀ Q ∈ (Ideal.span {algebraMap R ↥(chartAlgInf R F j) ϖ}).minimalPrimes,
      (jInvChartInf R F j : ↥(chartAlgInf R F j)) ∉ Q) :
    (irreducibleComponents ↥(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))).ncard =
      (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes.ncard := by
  classical

  let 𝒰 : (AlgebraicCurve.TwoChartIntegralModel R F j).OpenCover :=
    Scheme.Cover.mkOfCovers Bool (fun b => @Bool.rec (fun _ => Scheme.{u}) (XInf R F j) (XFin R F j) b)
      (fun b => match b with
        | true => ιFin R F j
        | false => ιInf R F j)
      (fun x => by
        rcases mem_range_ιFin_or_mem_range_ιInf R F j x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact ⟨true, y, hy⟩
        · exact ⟨false, y, hy⟩)
      (fun b => match b with
        | true => TwoChartIntegralModel.isOpenImmersion_ιFin R F j
        | false => TwoChartIntegralModel.isOpenImmersion_ιInf R F j)
  let 𝒱 := Scheme.Pullback.openCoverOfLeft 𝒰 (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))
  have hUt : 𝒰.f true = ιFin R F j := rfl
  have hUf : 𝒰.f false = ιInf R F j := rfl
  have h1 : ∀ b, 𝒱.f b ≫ pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) =
      pullback.fst _ _ ≫ 𝒰.f b := fun b => by
    simp only [𝒱, Scheme.Pullback.openCoverOfLeft_f]
    exact pullback.lift_fst _ _ _
  have h2 : ∀ b, Set.range (𝒱.f b).base =
      (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).base ⁻¹' Set.range (𝒰.f b).base := fun b => by
    simp only [𝒱, Scheme.Pullback.openCoverOfLeft_f]
    erw [Scheme.Pullback.range_map]
    simp

  obtain ⟨eFin, heFin⟩ := FibreComp.chart κ (AlgebraicCurve.TwoChartIntegralModel R F j) (toBase R F j) ↥(chartAlgFin R F j) (ιFin R F j)
    (ιFin_toBase R F j) (𝒱.f true) (h1 true)
  obtain ⟨eInf, heInf⟩ := FibreComp.chart κ (AlgebraicCurve.TwoChartIntegralModel R F j) (toBase R F j) ↥(chartAlgInf R F j) (ιInf R F j)
    (ιInf_toBase R F j) (𝒱.f false) (h1 false)

  have hsFin := FibreComp.includeLeft_surjective (R := R) ↥(chartAlgFin R F j) κ hsurj
  have hkFin := FibreComp.ker_includeLeft (R := R) ↥(chartAlgFin R F j) ϖ κ hsurj hker
  have hsInf := FibreComp.includeLeft_surjective (R := R) ↥(chartAlgInf R F j) κ hsurj
  have hkInf := FibreComp.ker_includeLeft (R := R) ↥(chartAlgInf R F j) ϖ κ hsurj hker

  have hmeet : ∀ Z ∈ irreducibleComponents ↥(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))), (Z ∩ Set.range (𝒱.f true).base).Nonempty := by
    intro Z hZ
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hZsub : Z ⊆ Set.range (𝒱.f false).base := by
      intro z hz
      have hcov : z ∈ Set.range (𝒱.f true).base ∨ z ∈ Set.range (𝒱.f false).base := by
        rw [h2, h2, Set.mem_preimage, Set.mem_preimage, hUt, hUf]
        exact mem_range_ιFin_or_mem_range_ιInf R F j _
      rcases hcov with h | h
      · have : z ∈ Z ∩ Set.range (𝒱.f true).base := ⟨hz, h⟩
        rw [hemp] at this
        exact absurd this (Set.notMem_empty _)
      · exact h
    have hIO : Topology.IsOpenEmbedding (𝒱.f false).base := (𝒱.f false).isOpenEmbedding
    obtain ⟨z₀, hz₀⟩ := hZ.1.1
    have hW : (𝒱.f false).base ⁻¹' Z ∈ irreducibleComponents _ :=
      preimage_mem_irreducibleComponents hZ hIO ⟨z₀, hz₀, hZsub hz₀⟩
    let φ := Scheme.homeoOfIso eInf
    set W' : Set (PrimeSpectrum (↥(chartAlgInf R F j) ⊗[R] κ)) := φ ⁻¹' ((𝒱.f false).base ⁻¹' Z) with hW'def
    have hW' : W' ∈ irreducibleComponents (PrimeSpectrum (↥(chartAlgInf R F j) ⊗[R] κ)) := by
      obtain ⟨w, hw⟩ := hW.1.1
      exact preimage_mem_irreducibleComponents hW φ.isOpenEmbedding ⟨w, hw, φ.symm w, φ.apply_symm_apply w⟩

    have hmin : PrimeSpectrum.vanishingIdeal W' ∈ minimalPrimes (↥(chartAlgInf R F j) ⊗[R] κ) := by
      rw [PrimeSpectrum.vanishingIdeal_mem_minimalPrimes, (isClosed_of_mem_irreducibleComponents _ hW').closure_eq]
      exact hW'
    let q : PrimeSpectrum (↥(chartAlgInf R F j) ⊗[R] κ) := ⟨PrimeSpectrum.vanishingIdeal W', hmin.1.1⟩
    have hqW' : q ∈ W' := by
      have hcl : W' = PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal W') := by
        rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, (isClosed_of_mem_irreducibleComponents _ hW').closure_eq]
      rw [hcl, PrimeSpectrum.mem_zeroLocus]

    have hz₁Z : (𝒱.f false).base (eInf.hom.base q) ∈ Z := hqW'
    have hfst : (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).base ((𝒱.f false).base (eInf.hom.base q)) =
        (ιInf R F j).base ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := ↥(chartAlgInf R F j)) (B := κ)))).base q) := by
      have := congrArg (fun h : Spec (CommRingCat.of (↥(chartAlgInf R F j) ⊗[R] κ)) ⟶ AlgebraicCurve.TwoChartIntegralModel R F j => h.base q) heInf
      simp at this
      exact this

    have hmem : ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := ↥(chartAlgInf R F j)) (B := κ)))).base q).asIdeal ∈
        (Ideal.span {algebraMap R ↥(chartAlgInf R F j) ϖ}).minimalPrimes := by
      rw [← hkInf, RingHom.ker_eq_comap_bot, Ideal.comap_minimalPrimes_eq_of_surjective hsInf]
      exact ⟨_, hmin, rfl⟩
    have hnot := hInf _ hmem
    have hrange : (ιInf R F j).base ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := ↥(chartAlgInf R F j)) (B := κ)))).base q) ∈ Set.range (ιFin R F j).base :=
      (iotaInf_mem_range_iotaFin_iff R F j _).mpr hnot
    have hin : (𝒱.f false).base (eInf.hom.base q) ∈ Set.range (𝒱.f true).base := by
      rw [h2, Set.mem_preimage, hUt, hfst]
      exact hrange
    have : (𝒱.f false).base (eInf.hom.base q) ∈ Z ∩ Set.range (𝒱.f true).base := ⟨hz₁Z, hin⟩
    rw [hemp] at this
    exact this

  calc (irreducibleComponents ↥(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))).ncard
      = (irreducibleComponents ↥(𝒱.X true)).ncard :=
        FibreComp.ncard_irreducibleComponents_eq_of_isOpenEmbedding (𝒱.f true).isOpenEmbedding hmeet
    _ = (irreducibleComponents (PrimeSpectrum (↥(chartAlgFin R F j) ⊗[R] κ))).ncard :=
        (FibreComp.ncard_irreducibleComponents_eq_of_homeomorph (Scheme.homeoOfIso eFin)).symm
    _ = (minimalPrimes (↥(chartAlgFin R F j) ⊗[R] κ)).ncard := FibreComp.ncard_irreducibleComponents_primeSpectrum _
    _ = (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes.ncard :=
        FibreComp.ncard_minimalPrimes_eq_of_surjective _ hsFin _ hkFin

end S_AlgebraicCurve_TwoChartIntegralModel_ncard_irreducibleComponents_pullback_toBase_eq_ncard_minimalPrimes_of_surjective
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_ncard_irreducibleComponents_pullback_toBase_eq_ncard_minimalPrimes_of_surjective (solution)

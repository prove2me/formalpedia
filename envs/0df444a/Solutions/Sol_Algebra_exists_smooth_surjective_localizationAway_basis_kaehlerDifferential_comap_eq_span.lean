-- Prove2me | solution 1 for Algebra.exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/8eb006e2-be41-5e7a-83e3-8d49731b74d2

import Mathlib
import Theorems.Thm_Algebra_exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField
import Theorems.Thm_Algebra_exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le
import Theorems.Thm_Module_FinitePresentation_exists_notMem_basis_localizedModule_of_basis_residueField_tensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span

set_option autoImplicit false

open TensorProduct KaehlerDifferential

universe u

namespace J3S1

theorem span_one_tmul_D_eq_top {R A κ : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing κ] [Algebra A κ] :
    Submodule.span κ (Set.range fun a : A => (1 : κ) ⊗ₜ[A] D R A a) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul c ω =>
    have hω : ω ∈ Submodule.span A (Set.range (D R A)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have : c ⊗ₜ[A] D R A a = c • ((1 : κ) ⊗ₜ[A] D R A a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [← TensorProduct.smul_tmul]
      have : (a • c) ⊗ₜ[A] x = (algebraMap A κ a) • (c ⊗ₜ[A] x) := by
        rw [TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul]
      rw [this]
      exact Submodule.smul_mem _ _ hx

theorem exists_b0 {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (J : Ideal A) (𝔭 : Ideal A) [𝔭.IsPrime] :
    ∃ (r n : ℕ) (yb : Fin r → A) (zb : Fin n → A), (∀ j, zb j ∈ J) ∧
      (∃ b₀ : Module.Basis (Fin r ⊕ Fin n) 𝔭.ResidueField (𝔭.ResidueField ⊗[A] Ω[A⁄R]),
        ∀ i, b₀ i = (1 : 𝔭.ResidueField) ⊗ₜ[A] D R A (Sum.elim yb zb i)) ∧
      (∀ z ∈ J, (1 : 𝔭.ResidueField) ⊗ₜ[A] D R A z ∈
        Submodule.span 𝔭.ResidueField (Set.range fun j : Fin n => (1 : 𝔭.ResidueField) ⊗ₜ[A] D R A (zb j))) := by
  classical
  set κ := 𝔭.ResidueField with hκ
  let v : A → κ ⊗[A] Ω[A⁄R] := fun a => (1 : κ) ⊗ₜ[A] D R A a

  obtain ⟨bJ, hbJJ, -, hJspan, hbJli⟩ :=
    exists_linearIndepOn_extension (K := κ) (v := v) (linearIndepOn_empty κ v) (Set.empty_subset (J : Set A))

  obtain ⟨b, -, hbJb, hspan, hbli⟩ := exists_linearIndepOn_extension (K := κ) (v := v) hbJli (Set.subset_univ bJ)

  have htop : ⊤ ≤ Submodule.span κ (Set.range fun i : b => v i) := by
    have hr : Set.range (fun i : b => v i) = v '' b := by
      ext x; simp
    rw [hr, ← span_one_tmul_D_eq_top (R := R) (A := A) (κ := κ), Submodule.span_le, ← Set.image_univ]
    exact hspan
  let B₀ : Module.Basis b κ (κ ⊗[A] Ω[A⁄R]) := Module.Basis.mk hbli htop
  haveI : Module.Finite κ (κ ⊗[A] Ω[A⁄R]) := inferInstance
  haveI : Finite b := Module.Finite.finite_basis B₀
  haveI : Finite (↥(b \ bJ) : Type u) := Finite.Set.subset b Set.diff_subset
  haveI : Finite (↥bJ : Type u) := Finite.Set.subset b hbJb
  letI : Fintype (↥(b \ bJ) : Type u) := Fintype.ofFinite _
  letI : Fintype (↥bJ : Type u) := Fintype.ofFinite _
  set r := Fintype.card (↥(b \ bJ) : Type u) with hr
  set n := Fintype.card (↥bJ : Type u) with hn
  let eR : (↥(b \ bJ) : Type u) ≃ Fin r := Fintype.equivFin _
  let eJ : (↥bJ : Type u) ≃ Fin n := Fintype.equivFin _
  let e' : Fin r ⊕ Fin n ≃ (b : Type u) :=
    ((Equiv.sumCongr eR.symm eJ.symm).trans (Equiv.sumComm _ _)).trans (Equiv.Set.sumDiffSubset hbJb)
  let yb : Fin r → A := fun i => ((eR.symm i : ↥(b \ bJ)) : A)
  let zb : Fin n → A := fun j => ((eJ.symm j : ↥bJ) : A)
  refine ⟨r, n, yb, zb, fun j => hbJJ (eJ.symm j).2, ⟨B₀.reindex e'.symm, fun i => ?_⟩, fun z hz => ?_⟩
  · rw [Module.Basis.reindex_apply, Equiv.symm_symm, Module.Basis.mk_apply]
    rcases i with i | j
    · simp [e', yb, v, Equiv.Set.sumDiffSubset_apply_inr]
    · simp [e', zb, v, Equiv.Set.sumDiffSubset_apply_inl]
  · have h1 : v z ∈ Submodule.span κ (v '' bJ) := hJspan ⟨z, hz, rfl⟩
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨eJ ⟨x, hx⟩, by simp [zb, v]⟩

theorem ker_lTensor_mapBaseChange_le_span {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (J : Ideal A) (κ : Type u) [Field κ] [Algebra (A ⧸ J) κ] [Algebra A κ] [IsScalarTower A (A ⧸ J) κ]
    (x : κ ⊗[A ⧸ J] ((A ⧸ J) ⊗[A] Ω[A⁄R]))
    (hx : LinearMap.lTensor κ (mapBaseChange R A (A ⧸ J)) x = 0) :
    x ∈ Submodule.span κ (Set.range fun z : J => (1 : κ) ⊗ₜ[A ⧸ J] ((1 : A ⧸ J) ⊗ₜ[A] D R A (z : A))) := by
  set B := A ⧸ J with hB
  set G := mapBaseChange R A B with hG
  have hGs : Function.Surjective G := mapBaseChange_surjective R A B Ideal.Quotient.mk_surjective
  have hex : Function.Exact (LinearMap.ker G).subtype G := LinearMap.exact_subtype_ker_map G
  have hexκ : Function.Exact (LinearMap.lTensor κ (LinearMap.ker G).subtype) (LinearMap.lTensor κ G) :=
    lTensor_exact (R := B) (M := LinearMap.ker G) (N := B ⊗[A] Ω[A⁄R]) (P := Ω[B⁄R]) κ hex hGs
  have hx' : x ∈ LinearMap.ker (LinearMap.lTensor κ G) := hx
  rw [hexκ.linearMap_ker_eq] at hx'
  obtain ⟨y, rfl⟩ := hx'
  clear hx

  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y₁ y₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | tmul c w =>
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply]
    have hw : (w : B ⊗[A] Ω[A⁄R]) ∈ LinearMap.range (kerCotangentToTensor R A B) := by
      rw [← (exact_kerCotangentToTensor_mapBaseChange R A B Ideal.Quotient.mk_surjective).linearMap_ker_eq]
      exact w.2
    obtain ⟨t, ht⟩ := hw
    obtain ⟨z, rfl⟩ := Ideal.toCotangent_surjective _ t
    rw [kerCotangentToTensor_toCotangent] at ht
    rw [← ht]
    have hz : (z : A) ∈ J := by
      have hz2 : algebraMap A B (z : A) = 0 := z.2
      exact Ideal.Quotient.eq_zero_iff_mem.mp hz2
    have : c ⊗ₜ[B] ((1 : B) ⊗ₜ[A] D R A (z : A)) = c • ((1 : κ) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] D R A (z : A))) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨z, hz⟩, rfl⟩)

noncomputable def kaehlerEquivOfSurjective {R : Type u} [CommRing R] (k : Type u) [Field k] [Algebra R k]
    (hk : Function.Surjective (algebraMap R k)) (B : Type u) [CommRing B] [Algebra R B] [Algebra k B] [IsScalarTower R k B] :
    Ω[B⁄R] ≃ₗ[B] Ω[B⁄k] :=
  LinearEquiv.ofBijective (KaehlerDifferential.map R k B B) ⟨by
    haveI : Subsingleton Ω[k⁄R] := subsingleton_of_surjective R k hk
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (exact_mapBaseChange_map R k B x).mp hx
    clear hx
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul b ω => rw [Subsingleton.elim ω 0, TensorProduct.tmul_zero, map_zero]
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, h₁, h₂, add_zero], KaehlerDifferential.map_surjective R k B⟩

private theorem _root_.J3S1.fibreBasis
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (k : Type u) [Field k] [Algebra R k] (hk : Function.Surjective (algebraMap R k))
    (J : Ideal A) [Algebra k (A ⧸ J)] [IsScalarTower R k (A ⧸ J)]
    (𝔭 : Ideal A) [𝔭.IsPrime] (𝔮 : Ideal (A ⧸ J)) [𝔮.IsPrime] (h𝔮 : 𝔮.comap (Ideal.Quotient.mk J) = 𝔭) :
    ∃ (r n : ℕ) (yb : Fin r → A) (zb : Fin n → A), (∀ j, zb j ∈ J) ∧
      (∃ b₀ : Module.Basis (Fin r ⊕ Fin n) 𝔭.ResidueField (𝔭.ResidueField ⊗[A] Ω[A⁄R]),
        ∀ i, b₀ i = (1 : 𝔭.ResidueField) ⊗ₜ[A] D R A (Sum.elim yb zb i)) ∧
      (∃ b₁ : Module.Basis (Fin r ⊕ Fin n) 𝔮.ResidueField (𝔮.ResidueField ⊗[A ⧸ J] ((A ⧸ J) ⊗[A] Ω[A⁄R])),
        ∀ i, b₁ i = (1 : 𝔮.ResidueField) ⊗ₜ[A ⧸ J] ((1 : A ⧸ J) ⊗ₜ[A] D R A (Sum.elim yb zb i))) ∧
      Module.finrank 𝔮.ResidueField (𝔮.ResidueField ⊗[A ⧸ J] Ω[(A ⧸ J)⁄k]) = r := by
  classical
  haveI : 𝔮.LiesOver 𝔭 := ⟨by rw [Ideal.under_def, ← h𝔮]; rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver 𝔭 𝔮
  obtain ⟨r, n, yb, zb, hzb, ⟨b₀, hb₀⟩, hJ⟩ := exists_b0 (R := R) J 𝔭

  let e1 : 𝔮.ResidueField ⊗[𝔭.ResidueField] (𝔭.ResidueField ⊗[A] Ω[A⁄R]) ≃ₗ[𝔮.ResidueField] 𝔮.ResidueField ⊗[A] Ω[A⁄R] := TensorProduct.AlgebraTensorModule.cancelBaseChange A 𝔭.ResidueField 𝔮.ResidueField 𝔮.ResidueField Ω[A⁄R]
  let e2 : 𝔮.ResidueField ⊗[A] Ω[A⁄R] ≃ₗ[𝔮.ResidueField] 𝔮.ResidueField ⊗[(A ⧸ J)] ((A ⧸ J) ⊗[A] Ω[A⁄R]) := (TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ J) 𝔮.ResidueField 𝔮.ResidueField Ω[A⁄R]).symm
  let b₁ : Module.Basis (Fin r ⊕ Fin n) 𝔮.ResidueField (𝔮.ResidueField ⊗[(A ⧸ J)] ((A ⧸ J) ⊗[A] Ω[A⁄R])) := (Algebra.TensorProduct.basis 𝔮.ResidueField b₀).map (e1.trans e2)
  have hb₁ : ∀ i, b₁ i = (1 : 𝔮.ResidueField) ⊗ₜ[(A ⧸ J)] ((1 : (A ⧸ J)) ⊗ₜ[A] D R A (Sum.elim yb zb i)) := by
    intro i
    simp only [b₁, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, hb₀, LinearEquiv.trans_apply, e1, e2]
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
  refine ⟨r, n, yb, zb, hzb, ⟨b₀, hb₀⟩, ⟨b₁, hb₁⟩, ?_⟩

  let G : 𝔮.ResidueField ⊗[(A ⧸ J)] ((A ⧸ J) ⊗[A] Ω[A⁄R]) →ₗ[𝔮.ResidueField] 𝔮.ResidueField ⊗[(A ⧸ J)] Ω[(A ⧸ J)⁄R] :=
    TensorProduct.AlgebraTensorModule.lTensor 𝔮.ResidueField 𝔮.ResidueField (mapBaseChange R A (A ⧸ J))
  have hGs : Function.Surjective G :=
    LinearMap.lTensor_surjective 𝔮.ResidueField (mapBaseChange_surjective R A (A ⧸ J) Ideal.Quotient.mk_surjective)

  have hK : LinearMap.ker G = Submodule.span 𝔮.ResidueField (Set.range (⇑b₁ ∘ Sum.inr)) := by
    apply le_antisymm
    · intro x hx
      have hx' := ker_lTensor_mapBaseChange_le_span (R := R) J 𝔮.ResidueField x hx
      refine Submodule.span_le.mpr ?_ hx'
      rintro _ ⟨z, rfl⟩

      let φ : 𝔭.ResidueField ⊗[A] Ω[A⁄R] →ₗ[𝔭.ResidueField] 𝔮.ResidueField ⊗[(A ⧸ J)] ((A ⧸ J) ⊗[A] Ω[A⁄R]) :=
        ((e1.trans e2).toLinearMap.restrictScalars 𝔭.ResidueField) ∘ₗ (TensorProduct.mk 𝔭.ResidueField 𝔮.ResidueField (𝔭.ResidueField ⊗[A] Ω[A⁄R]) 1)
      have hφ : ∀ a : A, φ ((1 : 𝔭.ResidueField) ⊗ₜ[A] D R A a) = (1 : 𝔮.ResidueField) ⊗ₜ[(A ⧸ J)] ((1 : (A ⧸ J)) ⊗ₜ[A] D R A a) := fun a => by
        simp only [φ, LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
          LinearEquiv.trans_apply, e1, e2]
        rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
      have h1 := Submodule.mem_map_of_mem (f := φ) (hJ z z.2)
      rw [hφ, Submodule.map_span] at h1
      refine (Submodule.span_le.mpr ?_ : _ ≤ (Submodule.span 𝔮.ResidueField (Set.range (⇑b₁ ∘ Sum.inr))).restrictScalars 𝔭.ResidueField) h1
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      rw [hφ]
      exact Submodule.subset_span ⟨j, by simp only [Function.comp_apply]; rw [hb₁]; rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show G (b₁ (Sum.inr j)) = 0
      rw [hb₁]
      show (1 : 𝔮.ResidueField) ⊗ₜ[(A ⧸ J)] (mapBaseChange R A (A ⧸ J) ((1 : (A ⧸ J)) ⊗ₜ[A] D R A (zb j))) = 0
      rw [mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D,
        show algebraMap A (A ⧸ J) (zb j) = 0 from (Ideal.Quotient.eq_zero_iff_mem.mpr (hzb j)), map_zero, TensorProduct.tmul_zero]
  have hfinK : Module.finrank 𝔮.ResidueField (LinearMap.ker G) = n := by
    rw [hK, finrank_span_eq_card (b₁.linearIndependent.comp Sum.inr Sum.inr_injective), Fintype.card_fin]
  have hfinW : Module.finrank 𝔮.ResidueField (𝔮.ResidueField ⊗[(A ⧸ J)] ((A ⧸ J) ⊗[A] Ω[A⁄R])) = r + n := by
    rw [Module.finrank_eq_card_basis b₁, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  haveI : Module.Finite 𝔮.ResidueField (𝔮.ResidueField ⊗[(A ⧸ J)] ((A ⧸ J) ⊗[A] Ω[A⁄R])) := Module.Finite.of_basis b₁
  have hrn := LinearMap.finrank_range_add_finrank_ker G
  rw [LinearMap.range_eq_top.mpr hGs, finrank_top, hfinK, hfinW] at hrn

  have eΩ : 𝔮.ResidueField ⊗[(A ⧸ J)] Ω[(A ⧸ J)⁄R] ≃ₗ[𝔮.ResidueField] 𝔮.ResidueField ⊗[(A ⧸ J)] Ω[(A ⧸ J)⁄k] :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl 𝔮.ResidueField 𝔮.ResidueField) (kaehlerEquivOfSurjective k hk (A ⧸ J))
  rw [← eΩ.finrank_eq]
  omega

p2m_export "J3S1" "fibreBasis"
end J3S1

namespace J3S2

private theorem _root_.J3S2.linIndep_of_basis_localizedModule
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (J : Ideal A) (t : A ⧸ J) {ι : Type} (w : ι → A)
    (bM : Module.Basis ι (Localization.Away t)
      (LocalizedModule (Submonoid.powers t) ((A ⧸ J) ⊗[A] Ω[A⁄R])))
    (hbM : ∀ i, bM i = LocalizedModule.mkLinearMap (Submonoid.powers t) ((A ⧸ J) ⊗[A] Ω[A⁄R])
      ((1 : A ⧸ J) ⊗ₜ[A] D R A (w i)))
    (S : Type u) [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower R A S]
    (M : Submonoid A) [IsLocalization M S]
    (ht : IsUnit (algebraMap (A ⧸ J) (S ⧸ J.map (algebraMap A S)) t)) :
    LinearIndependent (S ⧸ J.map (algebraMap A S))
      fun i : ι => (1 : S ⧸ J.map (algebraMap A S)) ⊗ₜ[S] D R S (algebraMap A S (w i)) := by

  letI algLS' : Algebra (Localization.Away t) (S ⧸ J.map (algebraMap A S)) :=
    (Localization.awayLift (algebraMap (A ⧸ J) (S ⧸ J.map (algebraMap A S))) t ht).toAlgebra
  haveI : IsScalarTower (A ⧸ J) (Localization.Away t) (S ⧸ J.map (algebraMap A S)) :=
    IsScalarTower.of_algebraMap_eq fun b =>
      (IsLocalization.Away.lift_eq t ht b).symm

  haveI : Algebra.FormallyEtale A S := Algebra.FormallyEtale.of_isLocalization (Rₘ := S) M
  have hbc := IsLocalizedModule.isBaseChange (Submonoid.powers t) (Localization.Away t)
    (LocalizedModule.mkLinearMap (Submonoid.powers t) ((A ⧸ J) ⊗[A] Ω[A⁄R]))

  let E : (S ⧸ J.map (algebraMap A S)) ⊗[Localization.Away t] LocalizedModule (Submonoid.powers t) ((A ⧸ J) ⊗[A] Ω[A⁄R])
      ≃ₗ[S ⧸ J.map (algebraMap A S)] (S ⧸ J.map (algebraMap A S)) ⊗[S] Ω[S⁄R] :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (S ⧸ J.map (algebraMap A S)) _) hbc.equiv.symm).trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange (A ⧸ J) (Localization.Away t) (S ⧸ J.map (algebraMap A S))
      (S ⧸ J.map (algebraMap A S)) ((A ⧸ J) ⊗[A] Ω[A⁄R])).trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ J) (S ⧸ J.map (algebraMap A S))
      (S ⧸ J.map (algebraMap A S)) Ω[A⁄R]).trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A S (S ⧸ J.map (algebraMap A S))
      (S ⧸ J.map (algebraMap A S)) Ω[A⁄R]).symm.trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (S ⧸ J.map (algebraMap A S)) _)
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A S)))))
  have key : ∀ i, E ((1 : S ⧸ J.map (algebraMap A S)) ⊗ₜ[Localization.Away t] bM i) =
      (1 : S ⧸ J.map (algebraMap A S)) ⊗ₜ[S] D R S (algebraMap A S (w i)) := by
    intro i
    rw [hbM]
    simp only [E, LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
      IsBaseChange.equiv_symm_apply, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, KaehlerDifferential.map_D]
  have li := ((Algebra.TensorProduct.basis (S ⧸ J.map (algebraMap A S)) bM).map E).linearIndependent
  convert li using 1
  funext i
  rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, key]

p2m_export "J3S2" "linIndep_of_basis_localizedModule"
end J3S2

namespace J3S4

private theorem _root_.J3S4.centre_localized_smooth_and_rank
    (k : Type u) [Field k] (T : Type u) [CommRing T] [Algebra k T] [Algebra.FiniteType k T]
    (𝔮 : Ideal T) [𝔮.IsPrime] (hsmooth : Algebra.IsSmoothAt k 𝔮)
    (r : ℕ) (hrank : Module.finrank 𝔮.ResidueField (𝔮.ResidueField ⊗[T] Ω[T⁄k]) = r)
    (t : T) (ht : t ∉ 𝔮)
    (L : Type u) [CommRing L] [Algebra T L] [IsLocalization.Away t L]
    [Algebra k L] [IsScalarTower k T L] :
    ∃ (𝔮' : Ideal L) (_ : 𝔮'.IsPrime), 𝔮'.comap (algebraMap T L) = 𝔮 ∧
      Algebra.IsSmoothAt k 𝔮' ∧
      Module.finrank 𝔮'.ResidueField (𝔮'.ResidueField ⊗[L] Ω[L⁄k]) = r := by

  have hdisj : Disjoint (Submonoid.powers t : Set T) ↑𝔮 :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime t).mpr ht
  let 𝔮' : Ideal L := 𝔮.map (algebraMap T L)
  haveI h𝔮' : 𝔮'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers t) L 𝔮 inferInstance hdisj
  have hcomap : 𝔮'.comap (algebraMap T L) = 𝔮 :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers t) L inferInstance hdisj
  refine ⟨𝔮', h𝔮', hcomap, ?_, ?_⟩
  ·
    have hpt : PrimeSpectrum.comap (algebraMap T L) ⟨𝔮', h𝔮'⟩ = ⟨𝔮, inferInstance⟩ :=
      PrimeSpectrum.ext hcomap
    have hmem : (⟨𝔮', h𝔮'⟩ : PrimeSpectrum L) ∈ Algebra.smoothLocus k L := by
      rw [← Algebra.smoothLocus_comap_of_isLocalization (R := k) (A := T) t, Set.mem_preimage, hpt]
      exact hsmooth
    exact hmem
  ·
    haveI : Algebra.FormallyEtale T L := Algebra.FormallyEtale.of_isLocalization (Rₘ := L) (M := Submonoid.powers t)
    let κ := 𝔮.ResidueField
    let κ' := 𝔮'.ResidueField

    let j : κ →ₐ[T] κ' :=
      Ideal.ResidueField.mapₐ 𝔮 𝔮' (IsScalarTower.toAlgHom T T L) (by
        change 𝔮 = 𝔮'.comap (algebraMap T L)
        exact hcomap.symm)
    letI : Algebra κ κ' := j.toRingHom.toAlgebra
    haveI : IsScalarTower T κ κ' := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm

    let eΩ : L ⊗[T] Ω[T⁄k] ≃ₗ[L] Ω[L⁄k] := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k T L
    let e1 : κ' ⊗[L] Ω[L⁄k] ≃ₗ[κ'] κ' ⊗[L] (L ⊗[T] Ω[T⁄k]) :=
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κ' κ') eΩ.symm
    let e2 : κ' ⊗[L] (L ⊗[T] Ω[T⁄k]) ≃ₗ[κ'] κ' ⊗[T] Ω[T⁄k] :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange T L κ' κ' Ω[T⁄k]
    let e3 : κ' ⊗[T] Ω[T⁄k] ≃ₗ[κ'] κ' ⊗[κ] (κ ⊗[T] Ω[T⁄k]) :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange T κ κ' κ' Ω[T⁄k]).symm
    rw [(e1 ≪≫ₗ e2 ≪≫ₗ e3).finrank_eq, Module.finrank_baseChange, hrank]

p2m_export "J3S4" "centre_localized_smooth_and_rank"
end J3S4

namespace J3S3aStub

theorem smul_cotangent_eq_zero {C : Type u} [CommRing C] (I : Ideal C) {x : C} (hx : x ∈ I) (t : I.Cotangent) :
    x • t = 0 := by
  obtain ⟨y, rfl⟩ := I.toCotangent_surjective t
  rw [← map_smul, ← LinearMap.mem_ker, Ideal.mem_toCotangent_ker]
  simpa [pow_two] using Ideal.mul_mem_mul hx y.2

theorem formallySmooth_quotient_span_of_basis
    {R : Type u} [CommRing R] {C : Type u} [CommRing C] [Algebra R C] [Algebra.FormallySmooth R C]
    {r n : ℕ} (W : Fin r ⊕ Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R])
    (hb : ∀ i, b i = D R C (W i)) :
    Algebra.FormallySmooth R (C ⧸ Ideal.span (Set.range (W ∘ Sum.inr))) := by
  classical
  set I : Ideal C := Ideal.span (Set.range (W ∘ Sum.inr)) with hI
  set K : Ideal C := RingHom.ker (algebraMap C (C ⧸ I)) with hK
  have hKI : K = I := by rw [hK, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  have hz : ∀ j, W (Sum.inr j) ∈ K := fun j => by rw [hKI]; exact Ideal.subset_span ⟨j, rfl⟩
  rw [Algebra.FormallySmooth.iff_split_injection (R := R) (P := C) (A := C ⧸ I) Ideal.Quotient.mk_surjective]

  let lam : Ω[C⁄R] →ₗ[C] K.Cotangent :=
    b.constr C (fun i => Sum.elim (fun _ => (0 : K.Cotangent)) (fun j => K.toCotangent ⟨W (Sum.inr j), hz j⟩) i)
  have hlam : ∀ i, lam (b i) = Sum.elim (fun _ => (0 : K.Cotangent)) (fun j => K.toCotangent ⟨W (Sum.inr j), hz j⟩) i :=
    fun i => b.constr_basis C _ i

  have key' : ∀ (y : C), y ∈ Submodule.span C (Set.range (W ∘ Sum.inr)) →
      ∀ hy : y ∈ K, lam (D R C y) = K.toCotangent ⟨y, hy⟩ := by
    intro y hy'
    induction hy' using Submodule.span_induction with
    | mem x hx =>
      intro hxK
      obtain ⟨j, rfl⟩ := hx
      rw [show D R C ((W ∘ Sum.inr) j) = b (Sum.inr j) from (hb _).symm, hlam]
      rfl
    | zero =>
      intro h0
      rw [map_zero, map_zero, show (⟨0, h0⟩ : K) = 0 from rfl, map_zero]
    | add x x' hx hx' ihx ihx' =>
      intro h
      have hxK : x ∈ K := by rw [hKI]; exact hx
      have hxK' : x' ∈ K := by rw [hKI]; exact hx'
      rw [map_add, map_add, ihx hxK, ihx' hxK', ← map_add]
      rfl
    | smul a x hx ihx =>
      intro h
      have hxK : x ∈ K := by rw [hKI]; exact hx
      have hD : D R C (a • x) = a • D R C x + x • D R C a := by rw [smul_eq_mul, Derivation.leibniz]
      rw [hD, map_add, map_smul, map_smul, ihx hxK, smul_cotangent_eq_zero K hxK, add_zero, ← map_smul]
      rfl
  have key : ∀ (y : C) (hy : y ∈ K), lam (D R C y) = K.toCotangent ⟨y, hy⟩ := fun y hy =>
    key' y (by rw [hKI] at hy; exact hy) hy

  let f : C →ₗ[C] (Ω[C⁄R] →ₗ[C] K.Cotangent) := LinearMap.toSpanSingleton C _ lam
  have hf : I ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun ω => ?_
    show (x • lam) ω = 0
    rw [LinearMap.smul_apply]
    exact smul_cotangent_eq_zero K (by rw [hKI]; exact hx) _
  let μ : (C ⧸ I) →ₗ[C] (Ω[C⁄R] →ₗ[C] K.Cotangent) := Submodule.liftQ (I.restrictScalars C) f hf
  let l : (C ⧸ I) ⊗[C] Ω[C⁄R] →ₗ[C] K.Cotangent := TensorProduct.lift μ
  refine ⟨l, ?_⟩
  apply LinearMap.ext
  intro t
  obtain ⟨y, rfl⟩ := K.toCotangent_surjective t
  rw [LinearMap.comp_apply, LinearMap.id_apply, kerCotangentToTensor_toCotangent]
  show TensorProduct.lift μ ((1 : C ⧸ I) ⊗ₜ[C] D R C (y : C)) = K.toCotangent y
  rw [TensorProduct.lift.tmul]
  have : μ (1 : C ⧸ I) = lam := by
    show μ (Submodule.Quotient.mk (1 : C)) = lam
    rw [show μ (Submodule.Quotient.mk (1 : C)) = f 1 from Submodule.liftQ_apply _ _ _]
    simp [f]
  rw [this, key y y.2]

end J3S3aStub

namespace J3S3a

theorem quot_smooth
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {C : Type u} [CommRing C] [Algebra R C] (hC : Algebra.IsStandardSmooth R C)
    {r n : ℕ} (W : Fin r ⊕ Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R])
    (hb : ∀ i, b i = D R C (W i))
    (JC : Ideal C) (hJC : JC = Ideal.span (insert (algebraMap R C π) (Set.range (W ∘ Sum.inr))))
    [Algebra (IsLocalRing.ResidueField R) (C ⧸ JC)] [IsScalarTower R (IsLocalRing.ResidueField R) (C ⧸ JC)] :
    Algebra.FiniteType (IsLocalRing.ResidueField R) (C ⧸ JC) ∧
    Algebra.Smooth (IsLocalRing.ResidueField R) (C ⧸ JC) := by
  classical
  haveI : Algebra.IsStandardSmooth R C := hC
  haveI : Algebra.Smooth R C := inferInstance
  set I : Ideal C := Ideal.span (Set.range (W ∘ Sum.inr)) with hI
  have hIJ : I ≤ JC := by
    rw [hJC]; exact Ideal.span_mono (Set.subset_insert _ _)

  haveI : Algebra.FormallySmooth R (C ⧸ I) := J3S3aStub.formallySmooth_quotient_span_of_basis W b hb
  haveI : Algebra.FinitePresentation R (C ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  haveI : Algebra.Smooth R (C ⧸ I) := ⟨‹_›, ‹_›⟩

  have hk_surj : Function.Surjective (algebraMap R (IsLocalRing.ResidueField R)) := Ideal.Quotient.mk_surjective
  have hpizero : algebraMap R (IsLocalRing.ResidueField R) π = 0 := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff, hπ]
    exact Ideal.subset_span rfl
  haveI : Algebra.Smooth (IsLocalRing.ResidueField R) ((IsLocalRing.ResidueField R) ⊗[R] (C ⧸ I)) := inferInstance

  let g : C ⧸ I →ₐ[R] C ⧸ JC := Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ R JC) (fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ ha))
  let toF : (IsLocalRing.ResidueField R) ⊗[R] (C ⧸ I) →ₐ[(IsLocalRing.ResidueField R)] C ⧸ JC :=
    Algebra.TensorProduct.lift (Algebra.ofId (IsLocalRing.ResidueField R) (C ⧸ JC)) g (fun _ _ => Commute.all _ _)
  let g' : C →ₐ[R] (IsLocalRing.ResidueField R) ⊗[R] (C ⧸ I) := Algebra.TensorProduct.includeRight.comp (Ideal.Quotient.mkₐ R I)
  have hg' : ∀ a ∈ JC, g' a = 0 := by
    intro a ha
    rw [hJC] at ha
    have : JC ≤ RingHom.ker g'.toRingHom := by
      rw [hJC, Ideal.span_le]
      rintro x hx
      rw [SetLike.mem_coe, RingHom.mem_ker]
      rcases hx with rfl | ⟨j, rfl⟩
      · show (1 : (IsLocalRing.ResidueField R)) ⊗ₜ[R] (Ideal.Quotient.mk I (algebraMap R C π)) = 0
        rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
          ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, hpizero, TensorProduct.zero_tmul]
      · show (1 : (IsLocalRing.ResidueField R)) ⊗ₜ[R] (Ideal.Quotient.mk I ((W ∘ Sum.inr) j)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j)), TensorProduct.tmul_zero]
    exact this (hJC ▸ ha)
  let inv : C ⧸ JC →ₐ[R] (IsLocalRing.ResidueField R) ⊗[R] (C ⧸ I) := Ideal.Quotient.liftₐ JC g' hg'
  have hinv_to : ∀ x, inv (toF x) = x := by
    have : (inv.comp (toF.restrictScalars R)) = AlgHom.id R _ := by
      apply Algebra.TensorProduct.ext'
      intro a c
      obtain ⟨s, rfl⟩ := hk_surj a
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      have hsplit : algebraMap R (IsLocalRing.ResidueField R) s ⊗ₜ[R] (Ideal.Quotient.mk I c) =
          algebraMap R ((IsLocalRing.ResidueField R) ⊗[R] (C ⧸ I)) s *
            ((1 : (IsLocalRing.ResidueField R)) ⊗ₜ[R] Ideal.Quotient.mk I c) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hsplit, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes]
      congr 1
      rw [AlgHom.restrictScalars_apply]
      show inv (toF ((1 : (IsLocalRing.ResidueField R)) ⊗ₜ[R] (Ideal.Quotient.mk I c))) = _
      rw [Algebra.TensorProduct.lift_tmul]
      show inv (algebraMap (IsLocalRing.ResidueField R) (C ⧸ JC) 1 * g (Ideal.Quotient.mk I c)) = _
      rw [map_one, one_mul]
      rfl
    intro x
    exact congrArg (fun φ : (IsLocalRing.ResidueField R) ⊗[R] (C ⧸ I) →ₐ[R] (IsLocalRing.ResidueField R) ⊗[R] (C ⧸ I) => φ x) this
  have hto_surj : Function.Surjective toF := by
    intro y
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨(1 : (IsLocalRing.ResidueField R)) ⊗ₜ[R] Ideal.Quotient.mk I c, ?_⟩
    rw [Algebra.TensorProduct.lift_tmul]
    show algebraMap (IsLocalRing.ResidueField R) (C ⧸ JC) 1 * g (Ideal.Quotient.mk I c) = _
    rw [map_one, one_mul]
    rfl
  have hto_inj : Function.Injective toF := fun x y hxy => by
    rw [← hinv_to x, ← hinv_to y, hxy]
  let e : (IsLocalRing.ResidueField R) ⊗[R] (C ⧸ I) ≃ₐ[(IsLocalRing.ResidueField R)] C ⧸ JC := AlgEquiv.ofBijective toF ⟨hto_inj, hto_surj⟩
  haveI : Algebra.FormallySmooth (IsLocalRing.ResidueField R) (C ⧸ JC) := Algebra.FormallySmooth.of_equiv e
  haveI : Algebra.FinitePresentation (IsLocalRing.ResidueField R) (C ⧸ JC) := Algebra.FinitePresentation.equiv e
  exact ⟨inferInstance, ⟨‹_›, ‹_›⟩⟩

end J3S3a

namespace J3Body

private theorem _root_.J3Body.fibreBasis
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (k : Type u) [Field k] [Algebra R k] (hk : Function.Surjective (algebraMap R k))
    (J : Ideal A) [Algebra k (A ⧸ J)] [IsScalarTower R k (A ⧸ J)]
    (𝔭 : Ideal A) [𝔭.IsPrime] (𝔮 : Ideal (A ⧸ J)) [𝔮.IsPrime] (h𝔮 : 𝔮.comap (Ideal.Quotient.mk J) = 𝔭) :
    ∃ (r n : ℕ) (yb : Fin r → A) (zb : Fin n → A), (∀ j, zb j ∈ J) ∧
      (∃ b₀ : Module.Basis (Fin r ⊕ Fin n) 𝔭.ResidueField (𝔭.ResidueField ⊗[A] Ω[A⁄R]),
        ∀ i, b₀ i = (1 : 𝔭.ResidueField) ⊗ₜ[A] D R A (Sum.elim yb zb i)) ∧
      (∃ b₁ : Module.Basis (Fin r ⊕ Fin n) 𝔮.ResidueField (𝔮.ResidueField ⊗[A ⧸ J] ((A ⧸ J) ⊗[A] Ω[A⁄R])),
        ∀ i, b₁ i = (1 : 𝔮.ResidueField) ⊗ₜ[A ⧸ J] ((1 : A ⧸ J) ⊗ₜ[A] D R A (Sum.elim yb zb i))) ∧
      Module.finrank 𝔮.ResidueField (𝔮.ResidueField ⊗[A ⧸ J] Ω[(A ⧸ J)⁄k]) = r :=
  J3S1.fibreBasis k hk J 𝔭 𝔮 h𝔮

p2m_export "J3Body" "fibreBasis"

private theorem _root_.J3Body.linIndep_of_basis_localizedModule
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (J : Ideal A) (t : A ⧸ J) {ι : Type} (w : ι → A)
    (bM : Module.Basis ι (Localization.Away t)
      (LocalizedModule (Submonoid.powers t) ((A ⧸ J) ⊗[A] Ω[A⁄R])))
    (hbM : ∀ i, bM i = LocalizedModule.mkLinearMap (Submonoid.powers t) ((A ⧸ J) ⊗[A] Ω[A⁄R])
      ((1 : A ⧸ J) ⊗ₜ[A] D R A (w i)))
    (S : Type u) [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower R A S]
    (M : Submonoid A) [IsLocalization M S]
    (ht : IsUnit (algebraMap (A ⧸ J) (S ⧸ J.map (algebraMap A S)) t)) :
    LinearIndependent (S ⧸ J.map (algebraMap A S))
      fun i : ι => (1 : S ⧸ J.map (algebraMap A S)) ⊗ₜ[S] D R S (algebraMap A S (w i)) :=
  J3S2.linIndep_of_basis_localizedModule J t w bM hbM S M ht

p2m_export "J3Body" "linIndep_of_basis_localizedModule"

private theorem _root_.J3Body.quot_smooth
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {C : Type u} [CommRing C] [Algebra R C] (hC : Algebra.IsStandardSmooth R C)
    {r n : ℕ} (W : Fin r ⊕ Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R])
    (hb : ∀ i, b i = D R C (W i))
    (JC : Ideal C) (hJC : JC = Ideal.span (insert (algebraMap R C π) (Set.range (W ∘ Sum.inr))))
    [Algebra (IsLocalRing.ResidueField R) (C ⧸ JC)] [IsScalarTower R (IsLocalRing.ResidueField R) (C ⧸ JC)] :
    Algebra.FiniteType (IsLocalRing.ResidueField R) (C ⧸ JC) ∧
    Algebra.Smooth (IsLocalRing.ResidueField R) (C ⧸ JC) :=
  J3S3a.quot_smooth π hπ hC W b hb JC hJC

p2m_export "J3Body" "quot_smooth"
set_option maxHeartbeats 3200000 in
theorem quot_rank
    {R : Type u} [CommRing R]
    (π : R) (k : Type u) [Field k] [Algebra R k] (hk : Function.Surjective (algebraMap R k))
    {C : Type u} [CommRing C] [Algebra R C]
    {r n : ℕ} (W : Fin r ⊕ Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R])
    (hb : ∀ i, b i = D R C (W i))
    (JC : Ideal C) (hJC : JC = Ideal.span (insert (algebraMap R C π) (Set.range (W ∘ Sum.inr))))
    [Algebra k (C ⧸ JC)] [IsScalarTower R k (C ⧸ JC)]
    (v : Ideal (C ⧸ JC)) [v.IsPrime] :
    Module.finrank v.ResidueField (v.ResidueField ⊗[C ⧸ JC] Ω[(C ⧸ JC)⁄k]) ≤ r := by
  classical

  let u : Fin r → Ω[(C ⧸ JC)⁄k] := fun i => D k (C ⧸ JC) (algebraMap C (C ⧸ JC) (W (Sum.inl i)))
  have hz0 : ∀ j : Fin n, algebraMap C (C ⧸ JC) (W (Sum.inr j)) = 0 := by
    intro j
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, hJC]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩)
  have hspanB : Submodule.span (C ⧸ JC) (Set.range u) = ⊤ := by
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : D k (C ⧸ JC) (Ideal.Quotient.mk JC c) = KaehlerDifferential.map R k C (C ⧸ JC) (D R C c) := by
      rw [KaehlerDifferential.map_D]; rfl
    rw [SetLike.mem_coe, h1, ← b.sum_repr (D R C c), map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.map_smul_of_tower, hb, KaehlerDifferential.map_D]
    refine Submodule.smul_of_tower_mem _ _ ?_
    rcases i with i | j
    · exact Submodule.subset_span ⟨i, rfl⟩
    · rw [hz0 j, map_zero]; exact Submodule.zero_mem _

  let u' : Fin r → v.ResidueField ⊗[(C ⧸ JC)] Ω[(C ⧸ JC)⁄k] := fun i => (1 : v.ResidueField) ⊗ₜ[(C ⧸ JC)] u i
  have hspanv.ResidueField : Submodule.span v.ResidueField (Set.range u') = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul c ω =>
      have hω : ω ∈ Submodule.span (C ⧸ JC) (Set.range u) := by rw [hspanB]; trivial
      induction hω using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        have : c ⊗ₜ[(C ⧸ JC)] u i = c • u' i := by
          change c ⊗ₜ[(C ⧸ JC)] u i = c • ((1 : v.ResidueField) ⊗ₜ[(C ⧸ JC)] u i)
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        rw [← TensorProduct.smul_tmul]
        have : (a • c) ⊗ₜ[(C ⧸ JC)] x = (algebraMap (C ⧸ JC) v.ResidueField a) • (c ⊗ₜ[(C ⧸ JC)] x) := by
          rw [TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul]
        rw [this]
        exact Submodule.smul_mem _ _ hx
  rw [← finrank_top, ← hspanv.ResidueField]
  exact (finrank_range_le_card u').trans (by simp)

theorem quot_smooth_and_rank
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {C : Type u} [CommRing C] [Algebra R C] (hC : Algebra.IsStandardSmooth R C)
    {r n : ℕ} (W : Fin r ⊕ Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R])
    (hb : ∀ i, b i = D R C (W i))
    (JC : Ideal C) (hJC : JC = Ideal.span (insert (algebraMap R C π) (Set.range (W ∘ Sum.inr))))
    [Algebra (IsLocalRing.ResidueField R) (C ⧸ JC)] [IsScalarTower R (IsLocalRing.ResidueField R) (C ⧸ JC)] :
    Algebra.FiniteType (IsLocalRing.ResidueField R) (C ⧸ JC) ∧
    Algebra.Smooth (IsLocalRing.ResidueField R) (C ⧸ JC) ∧
    ∀ (v : Ideal (C ⧸ JC)) [v.IsPrime],
      Module.finrank v.ResidueField (v.ResidueField ⊗[C ⧸ JC] Ω[(C ⧸ JC)⁄IsLocalRing.ResidueField R]) ≤ r := by
  obtain ⟨h1, h2⟩ := quot_smooth π hπ hC W b hb JC hJC
  exact ⟨h1, h2, fun v _ => quot_rank π (IsLocalRing.ResidueField R) Ideal.Quotient.mk_surjective W b hb JC hJC v⟩

private theorem _root_.J3Body.centre_localized_smooth_and_rank
    (k : Type u) [Field k] (T : Type u) [CommRing T] [Algebra k T] [Algebra.FiniteType k T]
    (𝔮 : Ideal T) [𝔮.IsPrime] (hsmooth : Algebra.IsSmoothAt k 𝔮)
    (r : ℕ) (hrank : Module.finrank 𝔮.ResidueField (𝔮.ResidueField ⊗[T] Ω[T⁄k]) = r)
    (t : T) (ht : t ∉ 𝔮)
    (L : Type u) [CommRing L] [Algebra T L] [IsLocalization.Away t L]
    [Algebra k L] [IsScalarTower k T L] :
    ∃ (𝔮' : Ideal L) (_ : 𝔮'.IsPrime), 𝔮'.comap (algebraMap T L) = 𝔮 ∧
      Algebra.IsSmoothAt k 𝔮' ∧
      Module.finrank 𝔮'.ResidueField (𝔮'.ResidueField ⊗[L] Ω[L⁄k]) = r :=
  J3S4.centre_localized_smooth_and_rank k T 𝔮 hsmooth r hrank t ht L

p2m_export "J3Body" "centre_localized_smooth_and_rank"
end J3Body

namespace J3Body

theorem linearIndependent_of_semilinear
    {R₁ R₂ : Type*} [Ring R₁] [Ring R₂] {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R₁ M₁] [Module R₂ M₂] (σ : R₁ →+* R₂) (hσ : Function.Injective σ)
    (j : M₁ →+ M₂) (hj : ∀ (r : R₁) (m : M₁), j (r • m) = σ r • j m)
    {ι : Type*} (v : ι → M₁) (hv : LinearIndependent R₂ (j ∘ v)) : LinearIndependent R₁ v := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  have h := congrArg j hg
  rw [map_sum, map_zero] at h
  simp_rw [hj] at h
  have := hv s (fun i => σ (g i)) (by simpa using h) i hi
  exact hσ ((show σ (g i) = 0 from this).trans (map_zero σ).symm)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem finalTransport
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) {A : Type u} [CommRing A] [Algebra R A]
    (J : Ideal A) (𝔭 : Ideal A) [𝔭.IsPrime]
    {r n : ℕ} (yb : Fin r → A) (zb : Fin n → A)
    (g₁ : A) (hg₁ : g₁ ∉ 𝔭) (C : Type u) [CommRing C] [Algebra R C]
    [Algebra C (Localization.Away g₁)] [IsScalarTower R C (Localization.Away g₁)]
    (hCstd : Algebra.IsStandardSmooth R C) (hθ : Function.Surjective (algebraMap C (Localization.Away g₁)))
    (W : Fin r ⊕ Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R])
    (hW : ∀ i, algebraMap C (Localization.Away g₁) (W i) = algebraMap A (Localization.Away g₁) (Sum.elim yb zb i))
    (hb : ∀ i, b i = D R C (W i))
    (c : C) (a : A) (ha : a ∉ 𝔭) (hca : algebraMap C (Localization.Away g₁) c = algebraMap A (Localization.Away g₁) a)
    (hIdeal : (Ideal.comap (algebraMap C (Localization.Away g₁)) (J.map (algebraMap A (Localization.Away g₁)))).map
        (algebraMap C (Localization.Away c)) =
      (Ideal.span (insert (algebraMap R C π) (Set.range (W ∘ Sum.inr)))).map (algebraMap C (Localization.Away c)))
    (g₂ : A) (hg₂a : g₂ ∣ a)
    (hlinS : ∀ (S : Type u) [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower R A S]
      (M : Submonoid A) [IsLocalization M S],
      IsUnit (algebraMap A S g₂) →
      LinearIndependent (S ⧸ J.map (algebraMap A S))
        fun j : Fin n => (1 : S ⧸ J.map (algebraMap A S)) ⊗ₜ[S] D R S (algebraMap A S (zb j))) :
    ∃ (g : A) (_ : g ∉ 𝔭) (r n : ℕ) (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra C (Localization.Away g)) (_ : IsScalarTower R C (Localization.Away g)),
      Algebra.Smooth R C ∧ Function.Surjective (algebraMap C (Localization.Away g)) ∧
      ∃ (y : Fin r → C) (z : Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R]),
        (∀ i, b (Sum.inl i) = D R C (y i)) ∧ (∀ j, b (Sum.inr j) = D R C (z j)) ∧
        Ideal.comap (algebraMap C (Localization.Away g)) (J.map (algebraMap A (Localization.Away g))) =
          Ideal.span (insert (algebraMap R C π) (Set.range z)) ∧
        LinearIndependent (C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z)))
          fun j : Fin n => (1 : C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z))) ⊗ₜ[C]
            D R (Localization.Away g) (algebraMap C (Localization.Away g) (z j)) := by
  classical

  let θ : C →ₐ[R] (Localization.Away g₁) := ⟨algebraMap C (Localization.Away g₁), fun r' => (IsScalarTower.algebraMap_apply R C (Localization.Away g₁) r').symm⟩
  haveI hAwayθc : IsLocalization.Away (θ c) (Localization.Away (algebraMap A (Localization.Away g₁) a)) := by
    change IsLocalization.Away (algebraMap C (Localization.Away g₁) c) (Localization.Away (algebraMap A (Localization.Away g₁) a)); rw [hca]; infer_instance
  let φT : (Localization.Away c) →ₐ[R] (Localization.Away (algebraMap A (Localization.Away g₁) a)) := IsLocalization.Away.mapₐ (Localization.Away c) (Localization.Away (algebraMap A (Localization.Away g₁) a)) θ c
  have hφT_surj : Function.Surjective φT := IsLocalization.Away.mapₐ_surjective_of_surjective c hθ
  have hφT_apply : ∀ x : C, φT (algebraMap C (Localization.Away c) x) = algebraMap (Localization.Away g₁) (Localization.Away (algebraMap A (Localization.Away g₁) a)) (algebraMap C (Localization.Away g₁) x) := by
    intro x
    rw [IsLocalization.Away.mapₐ_apply]
    exact IsLocalization.map_eq _ _

  let e : (Localization.Away (algebraMap A (Localization.Away g₁) a)) ≃ₐ[A] (Localization.Away (g₁ * a)) := IsLocalization.algEquiv (Submonoid.powers (g₁ * a)) (Localization.Away (algebraMap A (Localization.Away g₁) a)) (Localization.Away (g₁ * a))

  let φ : (Localization.Away c) →+* (Localization.Away (g₁ * a)) := (e : (Localization.Away (algebraMap A (Localization.Away g₁) a)) →+* (Localization.Away (g₁ * a))).comp φT.toRingHom
  letI iCSg : Algebra (Localization.Away c) (Localization.Away (g₁ * a)) := φ.toAlgebra
  have hφ_alg : ∀ x : (Localization.Away c), algebraMap (Localization.Away c) (Localization.Away (g₁ * a)) x = e (φT x) := fun _ => rfl
  have hφC : ∀ x : C, algebraMap (Localization.Away c) (Localization.Away (g₁ * a)) (algebraMap C (Localization.Away c) x) = e (algebraMap (Localization.Away g₁) (Localization.Away (algebraMap A (Localization.Away g₁) a)) (algebraMap C (Localization.Away g₁) x)) := by
    intro x; rw [hφ_alg, hφT_apply]
  have heA₁ : ∀ y : A, e (algebraMap (Localization.Away g₁) (Localization.Away (algebraMap A (Localization.Away g₁) a)) (algebraMap A (Localization.Away g₁) y)) = algebraMap A (Localization.Away (g₁ * a)) y := by
    intro y
    rw [← IsScalarTower.algebraMap_apply A (Localization.Away g₁) (Localization.Away (algebraMap A (Localization.Away g₁) a))]
    exact e.commutes y
  haveI : IsScalarTower R (Localization.Away c) (Localization.Away (g₁ * a)) := IsScalarTower.of_algebraMap_eq' (by
    ext r'
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R C (Localization.Away c), hφC,
      ← IsScalarTower.algebraMap_apply R C (Localization.Away g₁), IsScalarTower.algebraMap_apply R A (Localization.Away g₁), heA₁,
      IsScalarTower.algebraMap_apply R A (Localization.Away (g₁ * a))])

  haveI : Algebra.IsStandardSmooth R C := hCstd
  haveI : Algebra.IsStandardSmooth C (Localization.Away c) := Algebra.IsStandardSmooth.localization_away c
  haveI : Algebra.IsStandardSmooth R (Localization.Away c) := Algebra.IsStandardSmooth.trans R C (Localization.Away c)
  have hCsm : Algebra.Smooth R (Localization.Away c) := inferInstance

  have hsurj : Function.Surjective (algebraMap (Localization.Away c) (Localization.Away (g₁ * a))) := by
    intro s; obtain ⟨t, rfl⟩ := e.surjective s; obtain ⟨x, rfl⟩ := hφT_surj t; exact ⟨x, rfl⟩

  let z' : Fin n → (Localization.Away c) := fun j => algebraMap C (Localization.Away c) (W (Sum.inr j))

  let b' : Module.Basis (Fin r ⊕ Fin n) (Localization.Away c) Ω[(Localization.Away c)⁄R] :=
    b.ofIsLocalizedModule (Localization.Away c) (Submonoid.powers c) (KaehlerDifferential.map R R C (Localization.Away c))
  have hb' : ∀ i, b' i = D R (Localization.Away c) (algebraMap C (Localization.Away c) (W i)) := by
    intro i
    rw [Module.Basis.ofIsLocalizedModule_apply, hb, KaehlerDifferential.map_D]

  have hz'S : ∀ j, algebraMap (Localization.Away c) (Localization.Away (g₁ * a)) (z' j) = algebraMap A (Localization.Away (g₁ * a)) (zb j) := by
    intro j; change algebraMap (Localization.Away c) (Localization.Away (g₁ * a)) (algebraMap C (Localization.Away c) (W (Sum.inr j))) = _; rw [hφC, hW, Sum.elim_inr, heA₁]

  have hspan_map : (Ideal.span (insert (algebraMap R C π) (Set.range (W ∘ Sum.inr)))).map (algebraMap C (Localization.Away c)) =
      Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z')) := by
    rw [Ideal.map_span, Set.image_insert_eq, ← Set.range_comp, ← IsScalarTower.algebraMap_apply R C (Localization.Away c)]
    rfl
  have hmapJ : (J.map (algebraMap A (Localization.Away g₁))).map ((e : (Localization.Away (algebraMap A (Localization.Away g₁) a)) →+* (Localization.Away (g₁ * a))).comp (algebraMap (Localization.Away g₁) (Localization.Away (algebraMap A (Localization.Away g₁) a)))) =
      J.map (algebraMap A (Localization.Away (g₁ * a))) := by
    rw [Ideal.map_map]; congr 1; ext y; exact heA₁ y
  have hmem_e : ∀ (I : Ideal (Localization.Away (algebraMap A (Localization.Away g₁) a))) (y : (Localization.Away (algebraMap A (Localization.Away g₁) a))), e y ∈ I.map (e : (Localization.Away (algebraMap A (Localization.Away g₁) a)) →+* (Localization.Away (g₁ * a))) → y ∈ I := by
    intro I y hy
    have h := Ideal.mem_map_of_mem (e.symm : (Localization.Away (g₁ * a)) →+* (Localization.Away (algebraMap A (Localization.Away g₁) a))) hy
    rw [Ideal.map_map] at h
    have hcomp : (e.symm : (Localization.Away (g₁ * a)) →+* (Localization.Away (algebraMap A (Localization.Away g₁) a))).comp (e : (Localization.Away (algebraMap A (Localization.Away g₁) a)) →+* (Localization.Away (g₁ * a))) = RingHom.id _ := by
      ext t; simp
    rw [hcomp, Ideal.map_id] at h
    simpa using h
  have hJC' : Ideal.comap (algebraMap (Localization.Away c) (Localization.Away (g₁ * a))) (J.map (algebraMap A (Localization.Away (g₁ * a)))) =
      Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z')) := by
    rw [← hspan_map, ← hIdeal]
    apply le_antisymm
    · intro x' hx'
      rw [Ideal.mem_comap] at hx'
      obtain ⟨m, x, hmx⟩ := IsLocalization.Away.surj c x'
      have h1 : algebraMap (Localization.Away c) (Localization.Away (g₁ * a)) (algebraMap C (Localization.Away c) x) ∈ J.map (algebraMap A (Localization.Away (g₁ * a))) := by
        rw [← hmx, map_mul, map_pow]
        exact Ideal.mul_mem_right _ _ hx'
      rw [hφC, ← hmapJ, ← Ideal.map_map] at h1
      have h2 := hmem_e _ _ h1
      rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers (algebraMap A (Localization.Away g₁) a))] at h2
      obtain ⟨_, ⟨m', rfl⟩, hm'⟩ := h2
      beta_reduce at hm'
      rw [← hca, ← map_pow, ← map_mul] at hm'
      have h3 : c ^ m' * x ∈ Ideal.comap (algebraMap C (Localization.Away g₁)) (J.map (algebraMap A (Localization.Away g₁))) := by
        rw [Ideal.mem_comap]; exact hm'
      have h4 := Ideal.mem_map_of_mem (algebraMap C (Localization.Away c)) h3
      rw [map_mul, map_pow] at h4
      have hcu : IsUnit (algebraMap C (Localization.Away c) c ^ m') := (IsLocalization.Away.algebraMap_isUnit c).pow m'
      rw [Ideal.unit_mul_mem_iff_mem _ hcu] at h4
      have hcu' : IsUnit (algebraMap C (Localization.Away c) c ^ m) := (IsLocalization.Away.algebraMap_isUnit c).pow m
      rw [← Ideal.unit_mul_mem_iff_mem _ hcu', mul_comm, hmx]
      exact h4
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_comap, hφC, ← hmapJ, ← Ideal.map_map]
      apply Ideal.mem_map_of_mem
      apply Ideal.mem_map_of_mem
      rw [Ideal.mem_comap] at hx
      exact hx

  have hg₂unit : IsUnit (algebraMap A (Localization.Away (g₁ * a)) g₂) :=
    IsLocalization.Away.isUnit_of_dvd (g₁ * a) (hg₂a.trans (Dvd.intro_left g₁ rfl))
  have hlin0 := hlinS (Localization.Away (g₁ * a)) (Submonoid.powers (g₁ * a)) hg₂unit
  have hlin : LinearIndependent ((Localization.Away c) ⧸ Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z')))
      fun j : Fin n => (1 : (Localization.Away c) ⧸ Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z'))) ⊗ₜ[(Localization.Away c)]
        D R (Localization.Away (g₁ * a)) (algebraMap (Localization.Away c) (Localization.Away (g₁ * a)) (z' j)) := by
    have hle : Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z')) ≤ (J.map (algebraMap A (Localization.Away (g₁ * a)))).comap (algebraMap (Localization.Away c) (Localization.Away (g₁ * a))) :=
      hJC'.symm.le
    let σ : ((Localization.Away c) ⧸ Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z'))) →+* ((Localization.Away (g₁ * a)) ⧸ J.map (algebraMap A (Localization.Away (g₁ * a)))) :=
      Ideal.quotientMap (J.map (algebraMap A (Localization.Away (g₁ * a)))) (algebraMap (Localization.Away c) (Localization.Away (g₁ * a))) hle
    have hσmk : ∀ x : (Localization.Away c), σ (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap (Localization.Away c) (Localization.Away (g₁ * a)) x) :=
      fun x => Ideal.quotientMap_mk
    have hσ : Function.Injective σ := Ideal.quotientMap_injective' hJC'.le

    let j0 : ((Localization.Away c) ⧸ Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z'))) →+ (Ω[(Localization.Away (g₁ * a))⁄R] →+ (((Localization.Away (g₁ * a)) ⧸ J.map (algebraMap A (Localization.Away (g₁ * a)))) ⊗[(Localization.Away (g₁ * a))] Ω[(Localization.Away (g₁ * a))⁄R])) :=
      { toFun := fun x => (TensorProduct.mk (Localization.Away (g₁ * a)) ((Localization.Away (g₁ * a)) ⧸ J.map (algebraMap A (Localization.Away (g₁ * a)))) Ω[(Localization.Away (g₁ * a))⁄R] (σ x)).toAddMonoidHom
        map_zero' := by ext ω; simp
        map_add' := fun x y => by ext ω; simp }
    have hj0 : ∀ x ω, j0 x ω = σ x ⊗ₜ[(Localization.Away (g₁ * a))] ω := fun _ _ => rfl
    let j : ((Localization.Away c) ⧸ Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z'))) ⊗[(Localization.Away c)] Ω[(Localization.Away (g₁ * a))⁄R] →+ ((Localization.Away (g₁ * a)) ⧸ J.map (algebraMap A (Localization.Away (g₁ * a)))) ⊗[(Localization.Away (g₁ * a))] Ω[(Localization.Away (g₁ * a))⁄R] :=
      TensorProduct.liftAddHom j0 (fun r' x ω => by
        rw [hj0, hj0]
        obtain ⟨x0, rfl⟩ := Ideal.Quotient.mk_surjective x
        have e1 : r' • Ideal.Quotient.mk (Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z'))) x0 =
            Ideal.Quotient.mk _ (r' * x0) := rfl
        rw [e1, hσmk, hσmk, map_mul, ← algebraMap_smul (A := (Localization.Away (g₁ * a))) r' ω, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul']
        rfl)
    have hjt : ∀ (x : ((Localization.Away c) ⧸ Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z')))) (ω : Ω[(Localization.Away (g₁ * a))⁄R]), j (x ⊗ₜ ω) = σ x ⊗ₜ ω := fun x ω => by
      change j0 x ω = _; rw [hj0]
    letI instMQ : Module ((Localization.Away c) ⧸ Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z'))) (((Localization.Away c) ⧸ Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z'))) ⊗[(Localization.Away c)] Ω[(Localization.Away (g₁ * a))⁄R]) := TensorProduct.leftModule
    have hj : ∀ (r' : ((Localization.Away c) ⧸ Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z')))) (m : ((Localization.Away c) ⧸ Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z'))) ⊗[(Localization.Away c)] Ω[(Localization.Away (g₁ * a))⁄R]), j (r' • m) = σ r' • j m := by
      intro r' m
      induction m using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul x ω =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, hjt, hjt, map_mul, TensorProduct.smul_tmul', smul_eq_mul]
      | add m₁ m₂ h₁ h₂ => rw [smul_add, map_add, h₁, h₂, map_add, smul_add]
    refine linearIndependent_of_semilinear σ hσ j hj _ ?_
    have : (j ∘ fun j' : Fin n => (1 : ((Localization.Away c) ⧸ Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z')))) ⊗ₜ[(Localization.Away c)] D R (Localization.Away (g₁ * a)) (algebraMap (Localization.Away c) (Localization.Away (g₁ * a)) (z' j'))) =
        fun j' : Fin n => (1 : (Localization.Away (g₁ * a)) ⧸ J.map (algebraMap A (Localization.Away (g₁ * a)))) ⊗ₜ[(Localization.Away (g₁ * a))] D R (Localization.Away (g₁ * a)) (algebraMap A (Localization.Away (g₁ * a)) (zb j')) := by
      funext j'
      simp only [Function.comp_apply]
      rw [hjt, map_one, hz'S]
    rw [this]
    exact hlin0
  refine ⟨g₁ * a, fun h => (Ideal.IsPrime.mem_or_mem ‹𝔭.IsPrime› h).elim hg₁ ha, r, n, (Localization.Away c), inferInstance,
    inferInstance, iCSg, inferInstance, hCsm, hsurj, fun i => algebraMap C (Localization.Away c) (W (Sum.inl i)), z', b',
    fun i => hb' (Sum.inl i), fun j => hb' (Sum.inr j), hJC', hlin⟩

end J3Body

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (J : Ideal A) (hπJ : algebraMap R A π ∈ J)
    [Algebra (IsLocalRing.ResidueField R) (A ⧸ J)] [IsScalarTower R (IsLocalRing.ResidueField R) (A ⧸ J)]
    (𝔭 : Ideal A) [𝔭.IsPrime]
    (𝔮 : Ideal (A ⧸ J)) [𝔮.IsPrime] (h𝔮 : 𝔮.comap (Ideal.Quotient.mk J) = 𝔭)
    (hsmooth : Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮)
    (hfree : (⟨𝔮, ‹_›⟩ : PrimeSpectrum (A ⧸ J)) ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] Ω[A⁄R])) :
    ∃ (g : A) (_ : g ∉ 𝔭) (r n : ℕ) (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra C (Localization.Away g)) (_ : IsScalarTower R C (Localization.Away g)),
      Algebra.Smooth R C ∧ Function.Surjective (algebraMap C (Localization.Away g)) ∧
      ∃ (y : Fin r → C) (z : Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R]),
        (∀ i, b (Sum.inl i) = D R C (y i)) ∧ (∀ j, b (Sum.inr j) = D R C (z j)) ∧
        Ideal.comap (algebraMap C (Localization.Away g)) (J.map (algebraMap A (Localization.Away g))) =
          Ideal.span (insert (algebraMap R C π) (Set.range z)) ∧
        LinearIndependent (C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z)))
          fun j : Fin n => (1 : C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z))) ⊗ₜ[C]
            D R (Localization.Away g) (algebraMap C (Localization.Away g) (z j)) := by
  classical
  set k : Type u := IsLocalRing.ResidueField R with hkdef
  haveI : IsNoetherianRing R := inferInstance
  haveI hAfp : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hk : Function.Surjective (algebraMap R k) := Ideal.Quotient.mk_surjective
  have hJ𝔭 : J ≤ 𝔭 := by
    intro x hx; rw [← h𝔮, Ideal.mem_comap]; rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact Ideal.zero_mem _

  obtain ⟨r, n, yb, zb, hzb, ⟨b₀, hb₀⟩, ⟨b₁, hb₁⟩, hrank⟩ := J3Body.fibreBasis k hk J 𝔭 𝔮 h𝔮

  obtain ⟨g₁, hg₁, C, iC, iRC, iCA, iT, hCstd, hθ, W, b, hW, hb⟩ :=
    Algebra.exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField
      𝔭 (Sum.elim yb zb) b₀ hb₀

  haveI : Module.FinitePresentation (A ⧸ J) ((A ⧸ J) ⊗[A] Ω[A⁄R]) := inferInstance
  obtain ⟨t, ht, bM, hbM⟩ :=
    Module.FinitePresentation.exists_notMem_basis_localizedModule_of_basis_residueField_tensor
      𝔮 hfree (fun i => (1 : A ⧸ J) ⊗ₜ[A] D R A (Sum.elim yb zb i)) b₁ hb₁
  obtain ⟨g₂, hg₂t⟩ := Ideal.Quotient.mk_surjective t
  have hg₂ : g₂ ∉ 𝔭 := by rw [← h𝔮, Ideal.mem_comap, hg₂t]; exact ht

  set A₁ : Type u := Localization.Away g₁ with hA₁
  set JC : Ideal C := Ideal.span (insert (algebraMap R C π) (Set.range (W ∘ Sum.inr))) with hJCdef
  set I₁ : Ideal C := Ideal.comap (algebraMap C A₁) (J.map (algebraMap A A₁)) with hI₁
  have hJCI : JC ≤ I₁ := by
    rw [hJCdef, Ideal.span_le]
    rintro x (rfl | ⟨j, rfl⟩)
    · change algebraMap R C π ∈ I₁
      rw [hI₁, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A A₁]
      exact Ideal.mem_map_of_mem _ hπJ
    · change W (Sum.inr j) ∈ I₁
      rw [hI₁, Ideal.mem_comap, hW]
      exact Ideal.mem_map_of_mem _ (hzb j)
  set B : Type u := C ⧸ JC with hB

  have hπB : ∀ x ∈ IsLocalRing.maximalIdeal R, algebraMap R B x = 0 := by
    intro x hx
    rw [hπ, Ideal.mem_span_singleton] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [map_mul, IsScalarTower.algebraMap_apply R C B, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _)), zero_mul]
  letI iKB : Algebra k B := (Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (algebraMap R B) hπB).toAlgebra
  haveI : IsScalarTower R k B := IsScalarTower.of_algebraMap_eq' (by
    ext x; change algebraMap R B x = Ideal.Quotient.lift _ _ hπB (Ideal.Quotient.mk _ x); simp)
  obtain ⟨hBft, hBsm, hBrank⟩ := J3Body.quot_smooth_and_rank π hπ hCstd W b hb JC hJCdef

  set gb₁ : A ⧸ J := Ideal.Quotient.mk J g₁ with hgb₁
  have hgb₁𝔮 : gb₁ ∉ 𝔮 := by rw [← h𝔮, Ideal.mem_comap] at hg₁; exact hg₁
  set L : Type u := Localization.Away gb₁ with hL
  haveI : Algebra.FiniteType R (A ⧸ J) := inferInstance
  haveI : Algebra.FiniteType k (A ⧸ J) := Algebra.FiniteType.of_restrictScalars_finiteType R k (A ⧸ J)
  obtain ⟨𝔮', i𝔮', h𝔮', hsm', hrank'⟩ :=
    J3Body.centre_localized_smooth_and_rank k (A ⧸ J) 𝔮 hsmooth r hrank gb₁ hgb₁𝔮 L

  have hunit : IsUnit (((algebraMap (A ⧸ J) L).comp (Ideal.Quotient.mk J)) g₁) :=
    IsLocalization.Away.algebraMap_isUnit gb₁
  set lam₁ : A₁ →+* L := IsLocalization.Away.lift g₁ hunit with hlam₁
  have hlam₁ : ∀ x : A, lam₁ (algebraMap A A₁ x) = algebraMap (A ⧸ J) L (Ideal.Quotient.mk J x) :=
    fun x => IsLocalization.Away.lift_eq g₁ hunit x
  set ψ₀ : C →+* L := lam₁.comp (algebraMap C A₁) with hψ₀
  have hlamJ : ∀ x ∈ J, lam₁ (algebraMap A A₁ x) = 0 := fun x hx => by
    rw [hlam₁, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  have hψ₀J : ∀ x ∈ JC, ψ₀ x = 0 := by
    have hle : JC ≤ RingHom.ker ψ₀ := by
      rw [hJCdef, Ideal.span_le]
      rintro x (rfl | ⟨j, rfl⟩)
      · simp only [SetLike.mem_coe, RingHom.mem_ker, hψ₀, RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply R C A₁, IsScalarTower.algebraMap_apply R A A₁]
        exact hlamJ _ hπJ
      · simp only [SetLike.mem_coe, RingHom.mem_ker, hψ₀, RingHom.comp_apply, Function.comp_apply]
        rw [hW, Sum.elim_inr]
        exact hlamJ _ (hzb j)
    exact fun x hx => hle hx
  set ψ₁ : B →+* L := Ideal.Quotient.lift JC ψ₀ hψ₀J with hψ₁
  have hψ₁k : ∀ x : k, ψ₁ (algebraMap k B x) = algebraMap k L x := by
    intro x
    obtain ⟨r', rfl⟩ := hk x
    rw [← IsScalarTower.algebraMap_apply R k B, IsScalarTower.algebraMap_apply R C B,
      Ideal.Quotient.algebraMap_eq, hψ₁, Ideal.Quotient.lift_mk, hψ₀, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply R C A₁, IsScalarTower.algebraMap_apply R A A₁, hlam₁,
      IsScalarTower.algebraMap_apply k (A ⧸ J) L, ← IsScalarTower.algebraMap_apply R k (A ⧸ J),
      IsScalarTower.algebraMap_apply R A (A ⧸ J), Ideal.Quotient.algebraMap_eq]
  let ψ : B →ₐ[k] L := AlgHom.mk ψ₁ hψ₁k
  have e1 : lam₁ (algebraMap A A₁ g₁) = algebraMap (A ⧸ J) L gb₁ :=
    (hlam₁ g₁).trans (congrArg (algebraMap (A ⧸ J) L) hgb₁).symm
  have hlam₁surj : Function.Surjective lam₁ := by
    intro zL
    obtain ⟨m, ā, hm⟩ := IsLocalization.Away.surj gb₁ zL
    obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective ā
    refine ⟨IsLocalization.mk' A₁ a₀ (⟨g₁ ^ m, m, rfl⟩ : Submonoid.powers g₁), ?_⟩
    have hu : IsUnit (algebraMap (A ⧸ J) L gb₁ ^ m) := (IsLocalization.Away.algebraMap_isUnit gb₁).pow m
    apply hu.mul_left_injective
    change lam₁ _ * algebraMap (A ⧸ J) L gb₁ ^ m = zL * algebraMap (A ⧸ J) L gb₁ ^ m
    rw [hm, ← e1, ← map_pow, ← map_mul, ← map_pow]
    erw [IsLocalization.mk'_spec]
    rw [hlam₁]
  have hψ : Function.Surjective ψ := by
    intro zL
    obtain ⟨y, hy⟩ := hlam₁surj zL
    obtain ⟨c, rfl⟩ := hθ y
    refine ⟨Ideal.Quotient.mk JC c, ?_⟩
    change ψ₁ (Ideal.Quotient.mk JC c) = zL
    rw [hψ₁, Ideal.Quotient.lift_mk, hψ₀, RingHom.comp_apply, hy]
  set v : Ideal B := 𝔮'.comap ψ.toRingHom with hv
  haveI : v.IsPrime := Ideal.comap_isPrime _ _

  haveI := hBft; haveI := hBsm
  obtain ⟨t₃, ht₃, hker⟩ :=
    Algebra.exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le
      ψ hψ 𝔮' v rfl hsm' ((hBrank v).trans hrank'.symm.le)

  have : ∃ (c : C) (a : A), a ∉ 𝔭 ∧ g₂ ∣ a ∧ algebraMap C A₁ c = algebraMap A A₁ a ∧
      (I₁.map (algebraMap C (Localization.Away c)) = JC.map (algebraMap C (Localization.Away c))) := by
    obtain ⟨c₃, rfl⟩ := Ideal.Quotient.mk_surjective t₃
    obtain ⟨m, a₃, hm⟩ := IsLocalization.Away.surj g₁ (algebraMap C A₁ c₃)
    obtain ⟨u₁, hu₁⟩ := hθ (algebraMap A A₁ (g₁ ^ m))
    obtain ⟨u₂, hu₂⟩ := hθ (algebraMap A A₁ g₂)

    have ha₃ : a₃ ∉ 𝔭 := by
      intro ha₃
      have h1 : lam₁ (algebraMap A A₁ a₃) ∈ 𝔮' := by
        rw [hlam₁]
        have : Ideal.Quotient.mk J a₃ ∈ 𝔮 := by rw [← h𝔮, Ideal.mem_comap] at ha₃; exact ha₃
        rw [← h𝔮'] at this
        exact this
      rw [← hm, map_mul, map_pow] at h1
      rcases (Ideal.IsPrime.mem_or_mem i𝔮' h1) with h2 | h2
      · apply ht₃
        rw [hv, Ideal.mem_comap]
        change ψ₁ (Ideal.Quotient.mk JC c₃) ∈ 𝔮'
        rwa [hψ₁, Ideal.Quotient.lift_mk, hψ₀, RingHom.comp_apply]
      · have hu : IsUnit (lam₁ (algebraMap A A₁ g₁) ^ m) := by
          rw [e1]; exact (IsLocalization.Away.algebraMap_isUnit gb₁).pow m
        exact (Ideal.IsPrime.ne_top i𝔮') (Ideal.eq_top_of_isUnit_mem _ h2 hu)
    refine ⟨c₃ * u₁ * u₂, a₃ * g₂, ?_, dvd_mul_left _ _, ?_, ?_⟩
    · exact fun h => (Ideal.IsPrime.mem_or_mem ‹𝔭.IsPrime› h).elim ha₃ hg₂
    · rw [map_mul, map_mul, hu₁, hu₂, map_mul, ← hm, map_pow]
    ·
      set Cc : Type u := Localization.Away (c₃ * u₁ * u₂) with hCc
      apply le_antisymm
      ·
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap]

        have hxker : Ideal.Quotient.mk JC x ∈ RingHom.ker ψ.toRingHom := by
          rw [RingHom.mem_ker]
          change ψ₁ (Ideal.Quotient.mk JC x) = 0
          rw [hψ₁, Ideal.Quotient.lift_mk, hψ₀, RingHom.comp_apply]
          rw [hI₁, Ideal.mem_comap] at hx
          have : J.map (algebraMap A A₁) ≤ RingHom.ker lam₁ := by
            rw [Ideal.map_le_iff_le_comap]; intro y hy; exact hlamJ y hy
          exact this hx
        have h0 : algebraMap B (Localization.Away (Ideal.Quotient.mk JC c₃)) (Ideal.Quotient.mk JC x) = 0 := by
          have := Ideal.mem_map_of_mem (algebraMap B (Localization.Away (Ideal.Quotient.mk JC c₃))) hxker
          rwa [hker, Ideal.mem_bot] at this
        rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (Ideal.Quotient.mk JC c₃))] at h0
        obtain ⟨⟨_, ⟨m', rfl⟩⟩, hm'⟩ := h0

        have hmem : c₃ ^ m' * x ∈ JC := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow]; exact hm'
        have hc₃unit : IsUnit (algebraMap C Cc (c₃ ^ m')) := by
          rw [map_pow]; refine IsUnit.pow _ ?_
          exact IsLocalization.Away.isUnit_of_dvd (c₃ * u₁ * u₂) ⟨u₁ * u₂, by ring⟩
        have := Ideal.mem_map_of_mem (algebraMap C Cc) hmem
        rw [map_mul] at this
        exact (Ideal.unit_mul_mem_iff_mem _ hc₃unit).mp this
      · exact Ideal.map_mono hJCI
  obtain ⟨c, a, ha, hg₂a, hca, hIdeal⟩ := this

  exact J3Body.finalTransport π J 𝔭 yb zb g₁ hg₁ C hCstd hθ W b hW hb c a ha hca hIdeal g₂ hg₂a
    (fun S _ _ _ _ M _ hu => J3Body.linIndep_of_basis_localizedModule J t (Sum.elim yb zb) bM hbM S M (by
        rw [← hg₂t]
        exact hu.map (algebraMap S (S ⧸ J.map (algebraMap A S)))) |>.comp Sum.inr Sum.inr_injective)

end S_Algebra_exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span
end P2MW
export P2MW.S_Algebra_exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span (solution)

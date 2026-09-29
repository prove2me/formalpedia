-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.ker_stalkMap_eq_branchIdeal_and_branchIdeal_sup_branchIdeal_eq_maximalIdeal_of_isReduced_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/5b44da90-a6b6-516d-b31a-1ec03ba3ac53

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_ker_stalkMap_eq_branchIdeal_and_branchIdeal_sup_branchIdeal_eq_maximalIdeal_of_isReduced_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

section Unit1

noncomputable section

namespace ECL_TransvPlumb

open IsLocalRing

private theorem surjective_fst_of_mem_range {C Z : Scheme} [IrreducibleSpace C] (i₁ i₂ : C ⟶ Z) [IsClosedImmersion i₂]
    (h : i₁.base (genericPoint C) ∈ Set.range ⇑i₂.base) :
    Function.Surjective ⇑(pullback.fst i₁ i₂).base := by
  have hsub : Set.range ⇑i₁.base ⊆ Set.range ⇑i₂.base := by
    have h1 : Set.range ⇑i₁.base = ⇑i₁.base '' closure {genericPoint C} := by
      rw [genericPoint_closure, Set.image_univ]
    rw [h1]
    refine (image_closure_subset_closure_image i₁.base.hom.continuous).trans ?_
    rw [Set.image_singleton]
    exact closure_minimal (Set.singleton_subset_iff.mpr h) i₂.isClosedEmbedding.isClosed_range
  intro c
  obtain ⟨c', hc'⟩ := hsub ⟨c, rfl⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) c c' hc'.symm
  exact ⟨z, hz⟩

private theorem surjective_snd_of_mem_range {C Z : Scheme} [IrreducibleSpace C] (i₁ i₂ : C ⟶ Z) [IsClosedImmersion i₁]
    (h : i₂.base (genericPoint C) ∈ Set.range ⇑i₁.base) :
    Function.Surjective ⇑(pullback.snd i₁ i₂).base := by
  have hsub : Set.range ⇑i₂.base ⊆ Set.range ⇑i₁.base := by
    have h1 : Set.range ⇑i₂.base = ⇑i₂.base '' closure {genericPoint C} := by
      rw [genericPoint_closure, Set.image_univ]
    rw [h1]
    refine (image_closure_subset_closure_image i₂.base.hom.continuous).trans ?_
    rw [Set.image_singleton]
    exact closure_minimal (Set.singleton_subset_iff.mpr h) i₁.isClosedEmbedding.isClosed_range
  intro c
  obtain ⟨c', hc'⟩ := hsub ⟨c, rfl⟩
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) c' c hc'
  exact ⟨z, hz⟩

end ECL_TransvPlumb

end

end Unit1

section Unit2

set_option autoImplicit false

open IsLocalRing AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ECL_Transv

private theorem fromSpecStalk_comap_closedPoint_spec {X : Scheme} {x ξ : X} (h : ξ ⤳ x) :
    X.fromSpecStalk x (PrimeSpectrum.comap (X.presheaf.stalkSpecializes h).hom (closedPoint (X.presheaf.stalk ξ))) =
      ξ := by
  have e := congrArg (fun f : Spec (X.presheaf.stalk ξ) ⟶ X => f (closedPoint (X.presheaf.stalk ξ)))
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) h)
  simpa only [Scheme.Hom.comp_apply, Spec.map_apply, Scheme.fromSpecStalk_closedPoint] using e

private theorem exists_specializes_and_eq_comap_stalkSpecializes {X : Scheme} (y : X)
    (𝔮 : Ideal (X.presheaf.stalk y)) [𝔮.IsPrime] :
    ∃ (z : X) (hz : z ⤳ y),
      𝔮 = Ideal.comap (X.presheaf.stalkSpecializes hz).hom (maximalIdeal (X.presheaf.stalk z)) := by
  let q : Spec (X.presheaf.stalk y) := ⟨𝔮, inferInstance⟩
  have hz : X.fromSpecStalk y q ⤳ y := by
    have hmem : X.fromSpecStalk y q ∈ Set.range (X.fromSpecStalk y) := ⟨q, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at hmem
  refine ⟨X.fromSpecStalk y q, hz, ?_⟩
  have hinj : Function.Injective (X.fromSpecStalk y) := (X.fromSpecStalk y).isEmbedding.injective
  have h1 := hinj (fromSpecStalk_comap_closedPoint_spec hz)
  exact (congrArg PrimeSpectrum.asIdeal h1).symm

private theorem comap_stalkSpecializes_refl_maximalIdeal {X : Scheme} (y : X) :
    Ideal.comap (X.presheaf.stalkSpecializes (specializes_refl y)).hom (maximalIdeal (X.presheaf.stalk y)) =
      maximalIdeal (X.presheaf.stalk y) := by
  simp

private theorem eq_maximalIdeal_or_eq_branchIdeal_or_eq_branchIdeal {C₁ C₂ X : Scheme} (i₁ : C₁ ⟶ X) (i₂ : C₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hsurj : ∀ z : X, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    (η₁ : C₁) (hη₁ : ∀ c : C₁, c ≠ η₁ → IsClosed ({c} : Set C₁))
    (η₂ : C₂) (hη₂ : ∀ c : C₂, c ≠ η₂ → IsClosed ({c} : Set C₂))
    {y : X} (h₁ : i₁.base η₁ ⤳ y) (h₂ : i₂.base η₂ ⤳ y)
    (𝔮 : Ideal (X.presheaf.stalk y)) [𝔮.IsPrime] :
    𝔮 = maximalIdeal (X.presheaf.stalk y) ∨ 𝔮 = Scheme.branchIdeal h₁ ∨ 𝔮 = Scheme.branchIdeal h₂ := by
  obtain ⟨z, hz, rfl⟩ := exists_specializes_and_eq_comap_stalkSpecializes y 𝔮
  rcases hsurj z with ⟨c, hc⟩ | ⟨c, hc⟩
  · by_cases hcη : c = η₁
    · subst hcη
      subst hc
      exact Or.inr (Or.inl rfl)
    · have hcl : IsClosed ({z} : Set X) := by
        rw [← hc, ← Set.image_singleton]
        exact i₁.isClosedEmbedding.isClosedMap _ (hη₁ c hcη)
      have hyz : y = z := hz.mem_closed hcl (Set.mem_singleton z)
      subst hyz
      exact Or.inl (comap_stalkSpecializes_refl_maximalIdeal y)
  · by_cases hcη : c = η₂
    · subst hcη
      subst hc
      exact Or.inr (Or.inr rfl)
    · have hcl : IsClosed ({z} : Set X) := by
        rw [← hc, ← Set.image_singleton]
        exact i₂.isClosedEmbedding.isClosedMap _ (hη₂ c hcη)
      have hyz : y = z := hz.mem_closed hcl (Set.mem_singleton z)
      subst hyz
      exact Or.inl (comap_stalkSpecializes_refl_maximalIdeal y)

private theorem eq_of_branchIdeal_eq {X : Scheme} {x ξ₁ ξ₂ : X} (h₁ : ξ₁ ⤳ x) (h₂ : ξ₂ ⤳ x)
    (h : Scheme.branchIdeal h₁ = Scheme.branchIdeal h₂) : ξ₁ = ξ₂ := by
  have hpt : PrimeSpectrum.comap (X.presheaf.stalkSpecializes h₁).hom (closedPoint (X.presheaf.stalk ξ₁)) =
      PrimeSpectrum.comap (X.presheaf.stalkSpecializes h₂).hom (closedPoint (X.presheaf.stalk ξ₂)) :=
    PrimeSpectrum.ext h
  rw [← fromSpecStalk_comap_closedPoint_spec h₁, ← fromSpecStalk_comap_closedPoint_spec h₂, hpt]

private theorem specializes_of_branchIdeal_le {X : Scheme} {y ξ₁ ξ₂ : X} (h₁ : ξ₁ ⤳ y) (h₂ : ξ₂ ⤳ y)
    (hle : Scheme.branchIdeal h₁ ≤ Scheme.branchIdeal h₂) : ξ₁ ⤳ ξ₂ := by
  have hsp : (PrimeSpectrum.comap (X.presheaf.stalkSpecializes h₁).hom (closedPoint (X.presheaf.stalk ξ₁)) :
      Spec (X.presheaf.stalk y)) ⤳
        PrimeSpectrum.comap (X.presheaf.stalkSpecializes h₂).hom (closedPoint (X.presheaf.stalk ξ₂)) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hle
  have := hsp.map (X.fromSpecStalk y).continuous
  rwa [fromSpecStalk_comap_closedPoint_spec h₁, fromSpecStalk_comap_closedPoint_spec h₂] at this

private theorem branchIdeal_ne_maximalIdeal_and_not_le {C₁ C₂ X : Scheme} (i₁ : C₁ ⟶ X) (i₂ : C₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (η₁ : C₁) (hη₁ : ∀ c : C₁, c ≠ η₁ → IsClosed ({c} : Set C₁))
    (η₂ : C₂) (hη₂ : ∀ c : C₂, c ≠ η₂ → IsClosed ({c} : Set C₂))
    {y : X} (h₁ : i₁.base η₁ ⤳ y) (h₂ : i₂.base η₂ ⤳ y)
    (hne₁ : i₂.base η₂ ∉ Set.range i₁.base) (hne₂ : i₁.base η₁ ∉ Set.range i₂.base)
    (hy₁ : i₁.base η₁ ≠ y) (hy₂ : i₂.base η₂ ≠ y) :
    Scheme.branchIdeal h₁ ≠ maximalIdeal (X.presheaf.stalk y) ∧
      Scheme.branchIdeal h₂ ≠ maximalIdeal (X.presheaf.stalk y) ∧
      ¬ Scheme.branchIdeal h₁ ≤ Scheme.branchIdeal h₂ ∧ ¬ Scheme.branchIdeal h₂ ≤ Scheme.branchIdeal h₁ := by
  refine ⟨fun h => hy₁ ?_, fun h => hy₂ ?_, fun hle => ?_, fun hle => ?_⟩
  · exact eq_of_branchIdeal_eq h₁ (specializes_refl y) (h.trans (comap_stalkSpecializes_refl_maximalIdeal y).symm)
  · exact eq_of_branchIdeal_eq h₂ (specializes_refl y) (h.trans (comap_stalkSpecializes_refl_maximalIdeal y).symm)
  ·

    have hsp := specializes_of_branchIdeal_le h₁ h₂ hle
    exact hne₁ (hsp.mem_closed i₁.isClosedEmbedding.isClosed_range ⟨η₁, rfl⟩)
  · have hsp := specializes_of_branchIdeal_le h₂ h₁ hle
    exact hne₂ (hsp.mem_closed i₂.isClosedEmbedding.isClosed_range ⟨η₂, rfl⟩)

private theorem eq_branchIdeal_of_isPrime_of_le {X : Scheme} {y ξ₁ ξ₂ : X} (h₁ : ξ₁ ⤳ y) (h₂ : ξ₂ ⤳ y)
    (htri : ∀ 𝔮 : Ideal (X.presheaf.stalk y), 𝔮.IsPrime →
      𝔮 = maximalIdeal (X.presheaf.stalk y) ∨ 𝔮 = Scheme.branchIdeal h₁ ∨ 𝔮 = Scheme.branchIdeal h₂)
    (hP : Scheme.branchIdeal h₁ ≠ maximalIdeal (X.presheaf.stalk y))
    (hQP : ¬ Scheme.branchIdeal h₂ ≤ Scheme.branchIdeal h₁)
    (J : Ideal (X.presheaf.stalk y)) [hJp : J.IsPrime] (hJ : J ≤ Scheme.branchIdeal h₁) :
    J = Scheme.branchIdeal h₁ := by
  rcases htri J hJp with hm | hp | hq
  · subst hm
    exact absurd (le_antisymm (le_maximalIdeal (Scheme.branchIdeal_isPrime h₁).ne_top) hJ) hP
  · exact hp
  · subst hq
    exact absurd hJ hQP

end ECL_Transv

end Unit2

section Unit3

set_option autoImplicit false

open TensorProduct

private theorem eq_bot_of_forall_isPrime_le' {T : Type*} [CommRing T] [IsReduced T] {I : Ideal T}
    (h : ∀ 𝔮 : Ideal T, 𝔮.IsPrime → I ≤ 𝔮) : I = ⊥ := by
  refine le_bot_iff.mp ?_
  calc I ≤ sInf { J : Ideal T | J.IsPrime } := le_sInf fun 𝔮 h𝔮 => h 𝔮 h𝔮
    _ = nilradical T := (nilradical_eq_sInf T).symm
    _ = ⊥ := nilradical_eq_zero T

private theorem flat_quotient_map_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (P : Ideal A) : Module.Flat (A ⧸ P) (B ⧸ P.map (algebraMap A B)) :=
  Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B P).toLinearEquiv

private theorem isSMulRegular_quotient_map_of_notMem {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] (P : Ideal A) [P.IsPrime] {a : A} (ha : a ∉ P) :
    IsSMulRegular (B ⧸ P.map (algebraMap A B)) (algebraMap A (B ⧸ P.map (algebraMap A B)) a) := by
  haveI := flat_quotient_map_of_flat (A := A) (B := B) P
  have hreg : IsSMulRegular (A ⧸ P) (Ideal.Quotient.mk P a) :=
    mul_right_injective₀ (by simpa [Ideal.Quotient.eq_zero_iff_mem] using ha)
  have h := hreg.of_flat (S := B ⧸ P.map (algebraMap A B))
  rwa [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply] at h

private theorem map_eq_of_flat_of_forall_le {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [IsReduced B] (P : Ideal A) [P.IsPrime] {𝔭' : Ideal B}
    (h1 : P.map (algebraMap A B) ≤ 𝔭')
    (h2 : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮.comap (algebraMap A B) ≤ P → 𝔭' ≤ 𝔮) :
    P.map (algebraMap A B) = 𝔭' := by
  refine le_antisymm h1 fun q hq => ?_
  let S : Submonoid B := P.primeCompl.map (algebraMap A B)

  have hbot : 𝔭'.map (algebraMap B (Localization S)) = ⊥ := by
    refine eq_bot_of_forall_isPrime_le' fun 𝔔 h𝔔 => ?_
    obtain ⟨hprime, hdisj⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint S (Localization S) 𝔔).mp h𝔔
    refine Ideal.map_le_iff_le_comap.mpr (h2 _ hprime fun a ha => ?_)
    by_contra ha'
    exact Set.disjoint_left.mp hdisj (Submonoid.mem_map_of_mem (algebraMap A B) (ha' : a ∈ P.primeCompl))
      ha
  have hq0 : algebraMap B (Localization S) q = 0 := by
    have : algebraMap B (Localization S) q ∈ 𝔭'.map (algebraMap B (Localization S)) :=
      Ideal.mem_map_of_mem _ hq
    simpa [hbot] using this
  obtain ⟨⟨s, hs⟩, hsq⟩ := (IsLocalization.map_eq_zero_iff S (Localization S) q).mp hq0
  obtain ⟨a, ha, rfl⟩ := Submonoid.mem_map.mp hs

  have hreg := isSMulRegular_quotient_map_of_notMem (B := B) P (ha : a ∉ P)
  have hzero : algebraMap A (B ⧸ P.map (algebraMap A B)) a • Ideal.Quotient.mk _ q =
      algebraMap A (B ⧸ P.map (algebraMap A B)) a • (0 : B ⧸ P.map (algebraMap A B)) := by
    rw [smul_zero, smul_eq_mul, IsScalarTower.algebraMap_apply A B (B ⧸ P.map (algebraMap A B)),
      Ideal.Quotient.algebraMap_eq, ← map_mul]
    simpa using congrArg (Ideal.Quotient.mk (P.map (algebraMap A B))) hsq
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hreg hzero)

private theorem map_eq_of_flat_of_forall_le_ringHom {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (hψ : ψ.Flat) [IsReduced B] (P : Ideal A) [P.IsPrime] {𝔭' : Ideal B} (h1 : P.map ψ ≤ 𝔭')
    (h2 : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮.comap ψ ≤ P → 𝔭' ≤ 𝔮) : P.map ψ = 𝔭' := by
  letI : Algebra A B := ψ.toAlgebra
  haveI : Module.Flat A B := hψ
  exact map_eq_of_flat_of_forall_le P h1 h2

end Unit3

section Unit4

set_option autoImplicit false

private theorem eq_under_of_le_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (𝔭' : Ideal B) [𝔭'.IsPrime]
    (hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ 𝔭' → 𝔮 = 𝔭') {q : Ideal A} [q.IsPrime]
    (hle : q ≤ 𝔭'.under A) : q = 𝔭'.under A := by
  obtain ⟨𝔮, h𝔮le, h𝔮prime, h𝔮over⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := q) (q := 𝔭'.under A) 𝔭' hle
  rw [hmin 𝔮 h𝔮prime h𝔮le] at h𝔮over
  exact h𝔮over.over

private theorem eq_comap_of_le_of_flat_ringHom {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (hψ : ψ.Flat) (𝔭' : Ideal B) [𝔭'.IsPrime]
    (hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ 𝔭' → 𝔮 = 𝔭') {q : Ideal A} [q.IsPrime]
    (hle : q ≤ 𝔭'.comap ψ) : q = 𝔭'.comap ψ := by
  letI : Algebra A B := ψ.toAlgebra
  haveI : Module.Flat A B := hψ
  exact eq_under_of_le_of_flat 𝔭' hmin hle

private theorem not_le_comap_of_ne_of_flat_ringHom {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (hψ : ψ.Flat) (𝔭' : Ideal B) [𝔭'.IsPrime]
    (hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ 𝔭' → 𝔮 = 𝔭') {q : Ideal A} [q.IsPrime]
    (hne : q ≠ 𝔭'.comap ψ) : ¬ q ≤ 𝔭'.comap ψ :=
  fun hle => hne (eq_comap_of_le_of_flat_ringHom ψ hψ 𝔭' hmin hle)

end Unit4

section Unit5

set_option autoImplicit false

private theorem eq_of_isRadical_of_le_of_forall_le {B : Type*} [CommRing B] {I 𝔭 : Ideal B}
    (hI : I.IsRadical) [𝔭.IsPrime] (hle : I ≤ 𝔭)
    (hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → I ≤ 𝔮 → 𝔭 ≤ 𝔮) : I = 𝔭 := by
  refine le_antisymm hle ?_
  rw [← Ideal.radical_eq_iff.mpr hI, Ideal.radical_eq_sInf]
  exact le_sInf fun 𝔮 h𝔮 => hmin 𝔮 h𝔮.2 h𝔮.1

private theorem le_of_map_le_map_of_faithfullyFlat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] {I J : Ideal A}
    (h : I.map (algebraMap A B) ≤ J.map (algebraMap A B)) : I ≤ J := by
  calc I = (I.map (algebraMap A B)).comap (algebraMap A B) :=
        (Ideal.comap_map_eq_self_of_faithfullyFlat I).symm
    _ ≤ (J.map (algebraMap A B)).comap (algebraMap A B) := Ideal.comap_mono h
    _ = J := Ideal.comap_map_eq_self_of_faithfullyFlat J

private theorem le_of_map_le_map_of_flat_of_isLocalHom {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) (hf : f.Flat) [IsLocalHom f] {I J : Ideal A}
    (h : I.map f ≤ J.map f) : I ≤ J := by
  letI : Algebra A B := f.toAlgebra
  haveI : Module.Flat A B := hf
  haveI : IsLocalHom (algebraMap A B) := ‹IsLocalHom f›
  haveI : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact le_of_map_le_map_of_faithfullyFlat (A := A) (B := B) h

private theorem sup_eq_maximalIdeal_of_map_maximalIdeal_le {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) (hf : f.Flat) [IsLocalHom f] {P Q : Ideal A}
    (hP : P ≠ ⊤) (hQ : Q ≠ ⊤)
    (h : (IsLocalRing.maximalIdeal A).map f ≤ (P ⊔ Q).map f) :
    P ⊔ Q = IsLocalRing.maximalIdeal A :=
  le_antisymm (sup_le (IsLocalRing.le_maximalIdeal hP) (IsLocalRing.le_maximalIdeal hQ))
    (le_of_map_le_map_of_flat_of_isLocalHom f hf h)

end Unit5

section Unit6

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace

namespace TransvChair

variable {X Y : Scheme.{u}}

private theorem comap_stalkMap_comap_stalkSpecializes (f : X ⟶ Y) {ξ x : X} (h : ξ ⤳ x) :
    ((maximalIdeal (X.presheaf.stalk ξ)).comap (X.presheaf.stalkSpecializes h).hom).comap
        (f.stalkMap x).hom =
      (maximalIdeal (Y.presheaf.stalk (f.base ξ))).comap
        (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h)).hom := by
  rw [Ideal.comap_comap, ← CommRingCat.hom_comp, ← Scheme.Hom.stalkSpecializes_stalkMap f ξ x h,
    CommRingCat.hom_comp, ← Ideal.comap_comap, maximalIdeal_comap]

private theorem ker_stalkMap_le_comap_stalkSpecializes (f : X ⟶ Y) {ξ x : X} (h : ξ ⤳ x)
    [Nontrivial (X.presheaf.stalk ξ)] :
    RingHom.ker (f.stalkMap x).hom ≤
      (maximalIdeal (Y.presheaf.stalk (f.base ξ))).comap
        (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h)).hom := by
  intro s hs
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hu' := hu.map (f.stalkMap ξ).hom
  rw [Scheme.Hom.stalkSpecializes_stalkMap_apply f ξ x h, RingHom.mem_ker.mp hs, map_zero] at hu'
  exact not_isUnit_zero hu'

private theorem stalkSpecializes_surjective_of_eq {x x' : X} (e : x' = x) :
    Function.Surjective (X.presheaf.stalkSpecializes (specializes_of_eq e)).hom := by
  subst e
  intro t
  refine ⟨t, ?_⟩
  have : X.presheaf.stalkSpecializes (specializes_of_eq (rfl : x' = x')) = 𝟙 _ :=
    X.presheaf.stalkSpecializes_refl x'
  rw [this]
  rfl

private theorem isRadical_of_specLift {Z : Scheme.{u}} [IsReduced Z] (j : Z ⟶ X) (x : X)
    (K : Ideal (X.presheaf.stalk x)) [IsLocalRing ((X.presheaf.stalk x) ⧸ K)]
    [IsLocalHom (Ideal.Quotient.mk K)]
    (g : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ Z)
    (hg : g ≫ j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x)
    (hpt : (g ≫ j).base (closedPoint ((X.presheaf.stalk x) ⧸ K)) = x)
    (hK : K ≤ RingHom.ker ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)) ≫
        j.stalkMap (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K)))).hom) :
    K.IsRadical := by
  have claim : ∀ (f : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ X)
      (_ : f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x)
      (hfpt : f.base (closedPoint ((X.presheaf.stalk x) ⧸ K)) = x) (a : X.presheaf.stalk x),
      (Scheme.stalkClosedPointTo f).hom
          ((X.presheaf.stalkSpecializes (specializes_of_eq hfpt)).hom a) =
        Ideal.Quotient.mk K a := by
    intro f hf hfpt a
    subst hf
    obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
    have hqU : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x).base
        (closedPoint ((X.presheaf.stalk x) ⧸ K)) ∈ U := by
      rw [hfpt]
      exact hxU
    have e1 : (X.presheaf.stalkSpecializes (specializes_of_eq hfpt)).hom
          ((X.presheaf.germ U x hxU).hom s) =
        (X.presheaf.germ U _ hqU).hom s := by
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    rw [e1, ← CommRingCat.comp_apply, Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk]
    rfl
  rw [Ideal.isRadical_iff_quotient_reduced]
  refine ⟨fun r ⟨m, hm⟩ => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hb : (Scheme.stalkClosedPointTo g).hom
        ((j.stalkMap (g.base (closedPoint _))).hom
          ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a)) =
      Ideal.Quotient.mk K a := by
    have := claim (g ≫ j) hg hpt a
    rw [Scheme.stalkClosedPointTo_comp] at this
    simp only [CommRingCat.comp_apply] at this
    exact this
  have ham : a ^ m ∈ K := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
    exact hm
  have hbm := hK ham
  rw [RingHom.mem_ker, map_pow, CommRingCat.hom_comp, RingHom.comp_apply] at hbm
  have hb0 := IsReduced.eq_zero _ ⟨m, hbm⟩
  rw [← hb]
  erw [hb0]
  exact map_zero _

private theorem isRadical_comap_ker_sup_comap_ker {C₁ C₂ : Scheme.{u}}
    (i₁ : C₁ ⟶ X) (i₂ : C₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsReduced (pullback i₁ i₂)] (z : ↥(pullback i₁ i₂)) (x : X)
    (h₁ : i₁.base ((pullback.fst i₁ i₂).base z) = x)
    (h₂ : i₂.base ((pullback.snd i₁ i₂).base z) = x) :
    ((RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base z)).hom).comap
        (X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom ⊔
      (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base z)).hom).comap
        (X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom).IsRadical := by

  let σ₁ : X.presheaf.stalk x →+* C₁.presheaf.stalk ((pullback.fst i₁ i₂).base z) :=
    (i₁.stalkMap _).hom.comp (X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom
  let σ₂ : X.presheaf.stalk x →+* C₂.presheaf.stalk ((pullback.snd i₁ i₂).base z) :=
    (i₂.stalkMap _).hom.comp (X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom
  have hσ₁ : Function.Surjective σ₁ :=
    (i₁.stalkMap_surjective _).comp (stalkSpecializes_surjective_of_eq h₁)
  have hσ₂ : Function.Surjective σ₂ :=
    (i₂.stalkMap_surjective _).comp (stalkSpecializes_surjective_of_eq h₂)
  have hK₁ : RingHom.ker σ₁ =
      (RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base z)).hom).comap
        (X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom :=
    (RingHom.comap_ker _ _).symm
  have hK₂ : RingHom.ker σ₂ =
      (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base z)).hom).comap
        (X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom :=
    (RingHom.comap_ker _ _).symm
  set K := (RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base z)).hom).comap
      (X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom ⊔
    (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base z)).hom).comap
      (X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom with hKdef
  have hK₁le : RingHom.ker σ₁ ≤ K := hK₁ ▸ le_sup_left
  have hK₂le : RingHom.ker σ₂ ≤ K := hK₂ ▸ le_sup_right

  have hker₁ : RingHom.ker σ₁ ≤ maximalIdeal _ := by
    intro a ha
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map σ₁
    rw [RingHom.mem_ker.mp ha] at this
    exact not_isUnit_zero this
  have hker₂ : RingHom.ker σ₂ ≤ maximalIdeal _ := by
    intro a ha
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map σ₂
    rw [RingHom.mem_ker.mp ha] at this
    exact not_isUnit_zero this
  have hKmax : K ≤ maximalIdeal _ := sup_le (hK₁ ▸ hker₁) (hK₂ ▸ hker₂)
  have hKtop : K ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top (top_le_iff.mp (h ▸ hKmax))
  haveI : Nontrivial ((X.presheaf.stalk x) ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hKtop
  haveI : IsLocalRing ((X.presheaf.stalk x) ⧸ K) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk K) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

  let α₁ : C₁.presheaf.stalk ((pullback.fst i₁ i₂).base z) →+* (X.presheaf.stalk x) ⧸ K :=
    (Ideal.Quotient.factor hK₁le).comp (RingHom.quotientKerEquivOfSurjective hσ₁).symm.toRingHom
  let α₂ : C₂.presheaf.stalk ((pullback.snd i₁ i₂).base z) →+* (X.presheaf.stalk x) ⧸ K :=
    (Ideal.Quotient.factor hK₂le).comp (RingHom.quotientKerEquivOfSurjective hσ₂).symm.toRingHom
  have hα₁ : α₁.comp σ₁ = Ideal.Quotient.mk K := by
    ext a
    simp [α₁, RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.factor_mk]
  have hα₂ : α₂.comp σ₂ = Ideal.Quotient.mk K := by
    ext a
    simp [α₂, RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.factor_mk]
  haveI : IsLocalHom α₁ := IsLocalHom.of_surjective _
    (Function.Surjective.of_comp (g := σ₁) (by rw [← RingHom.coe_comp, hα₁]; exact Ideal.Quotient.mk_surjective))
  haveI : IsLocalHom α₂ := IsLocalHom.of_surjective _
    (Function.Surjective.of_comp (g := σ₂) (by rw [← RingHom.coe_comp, hα₂]; exact Ideal.Quotient.mk_surjective))

  let q : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ X :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x
  let a₁ : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ C₁ :=
    Spec.map (CommRingCat.ofHom α₁) ≫ C₁.fromSpecStalk _
  let a₂ : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ C₂ :=
    Spec.map (CommRingCat.ofHom α₂) ≫ C₂.fromSpecStalk _
  have hring₁ : (X.presheaf.stalkSpecializes (specializes_of_eq h₁)) ≫ i₁.stalkMap _ ≫ CommRingCat.ofHom α₁ =
      CommRingCat.ofHom (Ideal.Quotient.mk K) := by
    ext a
    change α₁ (σ₁ a) = Ideal.Quotient.mk K a
    rw [← RingHom.comp_apply, hα₁]
  have hring₂ : (X.presheaf.stalkSpecializes (specializes_of_eq h₂)) ≫ i₂.stalkMap _ ≫ CommRingCat.ofHom α₂ =
      CommRingCat.ofHom (Ideal.Quotient.mk K) := by
    ext a
    change α₂ (σ₂ a) = Ideal.Quotient.mk K a
    rw [← RingHom.comp_apply, hα₂]
  have ha₁ : a₁ ≫ i₁ = q := by
    simp only [a₁, q, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk]
    rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (specializes_of_eq h₁)]
    simp only [← Category.assoc, ← Spec.map_comp]
    rw [← hring₁]
    rfl
  have ha₂ : a₂ ≫ i₂ = q := by
    simp only [a₂, q, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk]
    rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (specializes_of_eq h₂)]
    simp only [← Category.assoc, ← Spec.map_comp]
    rw [← hring₂]
    rfl
  let g : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ pullback i₁ i₂ :=
    pullback.lift a₁ a₂ (ha₁.trans ha₂.symm)
  have hg : g ≫ (pullback.fst i₁ i₂ ≫ i₁) = q := by
    rw [← Category.assoc, pullback.lift_fst, ha₁]
  have hpt : (g ≫ (pullback.fst i₁ i₂ ≫ i₁)).base (closedPoint ((X.presheaf.stalk x) ⧸ K)) = x := by
    rw [hg]
    change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x)
      (closedPoint ((X.presheaf.stalk x) ⧸ K)) = x
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

  have hw₁ : (pullback.fst i₁ i₂).base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))) =
      (pullback.fst i₁ i₂).base z := by
    change (g ≫ pullback.fst i₁ i₂) (closedPoint ((X.presheaf.stalk x) ⧸ K)) = _
    rw [pullback.lift_fst]
    change (Spec.map (CommRingCat.ofHom α₁) ≫ C₁.fromSpecStalk _) (closedPoint _) = _
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have hw₂ : (pullback.snd i₁ i₂).base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))) =
      (pullback.snd i₁ i₂).base z := by
    change (g ≫ pullback.snd i₁ i₂) (closedPoint ((X.presheaf.stalk x) ⧸ K)) = _
    rw [pullback.lift_snd]
    change (Spec.map (CommRingCat.ofHom α₂) ≫ C₂.fromSpecStalk _) (closedPoint _) = _
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  refine isRadical_of_specLift (pullback.fst i₁ i₂ ≫ i₁) x K g hg hpt (sup_le ?_ ?_)
  ·
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    rw [RingHom.mem_ker]
    change ((pullback.fst i₁ i₂ ≫ i₁).stalkMap _).hom
      ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a) = 0
    have e : (X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a =
        ((X.presheaf.stalkSpecializes (specializes_of_eq h₁)) ≫ X.presheaf.stalkSpecializes
          (i₁.base.hom.map_specializes (specializes_of_eq hw₁))).hom a := by
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      rfl
    rw [Scheme.Hom.stalkMap_comp]
    change ((pullback.fst i₁ i₂).stalkMap _).hom ((i₁.stalkMap _).hom
      ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a)) = 0
    rw [e]
    change ((pullback.fst i₁ i₂).stalkMap _).hom ((i₁.stalkMap _).hom
      ((X.presheaf.stalkSpecializes (i₁.base.hom.map_specializes (specializes_of_eq hw₁))).hom
        ((X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom a))) = 0
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply i₁ _ _ (specializes_of_eq hw₁), ha, map_zero,
      map_zero]
  ·
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    rw [RingHom.mem_ker]
    change ((pullback.fst i₁ i₂ ≫ i₁).stalkMap _).hom
      ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a) = 0
    have hcond : (pullback.fst i₁ i₂ ≫ i₁).base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))) =
        (pullback.snd i₁ i₂ ≫ i₂).base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))) :=
      congrArg (fun k => k.base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))))
        (pullback.condition (f := i₁) (g := i₂))
    rw [Scheme.Hom.stalkMap_congr_hom _ _ pullback.condition, Scheme.Hom.stalkMap_comp]
    change ((pullback.snd i₁ i₂).stalkMap _).hom ((i₂.stalkMap _).hom
      (((X.presheaf.stalkSpecializes (specializes_of_eq hpt)) ≫
        (X.presheaf.stalkCongr (Inseparable.of_eq hcond)).hom).hom a)) = 0
    have e : ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)) ≫
          (X.presheaf.stalkCongr (Inseparable.of_eq hcond)).hom).hom a =
        ((X.presheaf.stalkSpecializes (specializes_of_eq h₂)) ≫
          X.presheaf.stalkSpecializes (i₂.base.hom.map_specializes (specializes_of_eq hw₂))).hom a := by
      change ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)) ≫
          X.presheaf.stalkSpecializes (Inseparable.of_eq hcond).ge).hom a = _
      rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_comp]
      rfl
    rw [e]
    change ((pullback.snd i₁ i₂).stalkMap _).hom ((i₂.stalkMap _).hom
      ((X.presheaf.stalkSpecializes (i₂.base.hom.map_specializes (specializes_of_eq hw₂))).hom
        ((X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom a))) = 0
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply i₂ _ _ (specializes_of_eq hw₂), ha, map_zero,
      map_zero]

private theorem branchIdeal_sup_eq_transport {x x' ζ₁ ζ₁' ζ₂ ζ₂' : X}
    (ex : x = x') (e₁ : ζ₁ = ζ₁') (e₂ : ζ₂ = ζ₂')
    (g₁ : ζ₁ ⤳ x) (g₂ : ζ₂ ⤳ x) (g₁' : ζ₁' ⤳ x') (g₂' : ζ₂' ⤳ x')
    (H : Scheme.branchIdeal g₁ ⊔ Scheme.branchIdeal g₂ = maximalIdeal (X.presheaf.stalk x)) :
    Scheme.branchIdeal g₁' ⊔ Scheme.branchIdeal g₂' = maximalIdeal (X.presheaf.stalk x') := by
  subst ex e₁ e₂
  exact H

private theorem descent {A Abar B : Type*} [CommRing A] [CommRing Abar] [CommRing B]
    [IsLocalRing A] [IsLocalRing Abar] [IsLocalRing B] [IsReduced B]
    (θ : A →+* Abar) (hθ : Function.Surjective θ) (ψ : Abar →+* B) (hψ : ψ.Flat) [IsLocalHom ψ]
    {P Q : Ideal A} {P' Q' : Ideal B} [P'.IsPrime] [Q'.IsPrime]
    (hP : P'.comap (ψ.comp θ) = P) (hQ : Q'.comap (ψ.comp θ) = Q) (hPQ : P ≠ Q)
    (htri : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 = maximalIdeal B ∨ 𝔮 = P' ∨ 𝔮 = Q')
    (hPm : P' ≠ maximalIdeal B) (hQm : Q' ≠ maximalIdeal B) (hPQ' : ¬ P' ≤ Q') (hQP' : ¬ Q' ≤ P')
    (hκ : P' ⊔ Q' = maximalIdeal B) :
    P ⊔ Q = maximalIdeal A := by
  haveI : IsLocalHom θ := IsLocalHom.of_surjective θ hθ

  have hminP : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ P' → 𝔮 = P' := by
    intro 𝔮 h𝔮 hle
    rcases htri 𝔮 h𝔮 with rfl | rfl | rfl
    · exact absurd ((maximalIdeal.isMaximal B).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
        hPm
    · rfl
    · exact absurd hle hQP'
  have hminQ : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ Q' → 𝔮 = Q' := by
    intro 𝔮 h𝔮 hle
    rcases htri 𝔮 h𝔮 with rfl | rfl | rfl
    · exact absurd ((maximalIdeal.isMaximal B).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
        hQm
    · exact absurd hle hPQ'
    · rfl

  have hkerP : RingHom.ker θ ≤ P := by
    intro a ha
    rw [← hP, Ideal.mem_comap, RingHom.comp_apply, RingHom.mem_ker.mp ha, map_zero]
    exact zero_mem _
  have hkerQ : RingHom.ker θ ≤ Q := by
    intro a ha
    rw [← hQ, Ideal.mem_comap, RingHom.comp_apply, RingHom.mem_ker.mp ha, map_zero]
    exact zero_mem _
  have hcmP : (P.map θ).comap θ = P := by
    rw [Ideal.comap_map_of_surjective _ hθ, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkerP]
  have hcmQ : (Q.map θ).comap θ = Q := by
    rw [Ideal.comap_map_of_surjective _ hθ, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkerQ]

  have hPbar : P'.comap ψ = P.map θ := by
    rw [← hP, ← Ideal.comap_comap, Ideal.map_comap_of_surjective θ hθ]
  have hQbar : Q'.comap ψ = Q.map θ := by
    rw [← hQ, ← Ideal.comap_comap, Ideal.map_comap_of_surjective θ hθ]
  haveI hPbp : (P.map θ).IsPrime := hPbar ▸ Ideal.comap_isPrime ψ P'
  haveI hQbp : (Q.map θ).IsPrime := hQbar ▸ Ideal.comap_isPrime ψ Q'
  have hPQbar : P.map θ ≠ Q.map θ := fun h => hPQ (by rw [← hcmP, h, hcmQ])

  have hmapP : (P.map θ).map ψ = P' := by
    refine map_eq_of_flat_of_forall_le_ringHom ψ hψ _ (Ideal.map_le_iff_le_comap.mpr hPbar.ge) ?_
    intro 𝔮 h𝔮 hle
    rcases htri 𝔮 h𝔮 with rfl | rfl | rfl
    · exact le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
    · exact le_rfl
    · exfalso
      rw [hQbar] at hle
      rw [← hPbar] at hle hPQbar
      exact not_le_comap_of_ne_of_flat_ringHom ψ hψ P' hminP hPQbar.symm hle
  have hmapQ : (Q.map θ).map ψ = Q' := by
    refine map_eq_of_flat_of_forall_le_ringHom ψ hψ _ (Ideal.map_le_iff_le_comap.mpr hQbar.ge) ?_
    intro 𝔮 h𝔮 hle
    rcases htri 𝔮 h𝔮 with rfl | rfl | rfl
    · exact le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
    · exfalso
      rw [hPbar] at hle
      rw [← hQbar] at hle hPQbar
      exact not_le_comap_of_ne_of_flat_ringHom ψ hψ Q' hminQ hPQbar hle
    · exact le_rfl

  have hbar : P.map θ ⊔ Q.map θ = maximalIdeal Abar := by
    refine sup_eq_maximalIdeal_of_map_maximalIdeal_le ψ hψ (Ideal.IsPrime.ne_top hPbp)
      (Ideal.IsPrime.ne_top hQbp) ?_
    rw [Ideal.map_sup, hmapP, hmapQ, hκ]
    exact Ideal.map_le_iff_le_comap.mpr (maximalIdeal_comap ψ).ge
  calc P ⊔ Q = ((P ⊔ Q).map θ).comap θ := by
        rw [Ideal.comap_map_of_surjective _ hθ, ← RingHom.ker_eq_comap_bot, eq_comm, sup_eq_left]
        exact hkerP.trans le_sup_left
    _ = maximalIdeal A := by rw [Ideal.map_sup, hbar, maximalIdeal_comap]

end TransvChair

end Unit6

section Unit7

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace

namespace TransvChair

variable {X Y : Scheme.{u}}

private theorem comap_stalkMap_branchIdeal (f : X ⟶ Y) {ξ x : X} (h : ξ ⤳ x) :
    (Scheme.branchIdeal h).comap (f.stalkMap x).hom = Scheme.branchIdeal (f.base.hom.map_specializes h) :=
  comap_stalkMap_comap_stalkSpecializes f h

private theorem isRadical_sup_of_ker_eq {C₁ C₂ : Scheme.{u}}
    (i₁ : C₁ ⟶ X) (i₂ : C₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsReduced (pullback i₁ i₂)] (z : ↥(pullback i₁ i₂))
    (h₂ : i₂.base ((pullback.snd i₁ i₂).base z) = i₁.base ((pullback.fst i₁ i₂).base z))
    {P Q : Ideal (X.presheaf.stalk (i₁.base ((pullback.fst i₁ i₂).base z)))}
    (hP : RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base z)).hom = P)
    (hQ : (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base z)).hom).comap
        (X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom = Q) :
    (P ⊔ Q).IsRadical := by
  subst hP hQ
  have h := isRadical_comap_ker_sup_comap_ker i₁ i₂ z _ rfl h₂
  have e : X.presheaf.stalkSpecializes (specializes_of_eq
      (rfl : i₁.base ((pullback.fst i₁ i₂).base z) = i₁.base ((pullback.fst i₁ i₂).base z))) = 𝟙 _ :=
    X.presheaf.stalkSpecializes_refl _
  rw [e, CommRingCat.hom_id, Ideal.comap_id] at h
  exact h

end TransvChair

end Unit7

section EngineU

noncomputable section

namespace X1TransvEngine

theorem surjective_fst_of_mem_range {C₁ C₂ Z : Scheme.{u}} [IrreducibleSpace C₁] (i₁ : C₁ ⟶ Z) (i₂ : C₂ ⟶ Z)
    [IsClosedImmersion i₂] (h : i₁.base (genericPoint C₁) ∈ Set.range i₂.base) :
    Function.Surjective (pullback.fst i₁ i₂).base := by
  have hsub : Set.range i₁.base ⊆ Set.range i₂.base := by
    have h1 : Set.range i₁.base = i₁.base '' closure {genericPoint C₁} := by
      rw [genericPoint_closure, Set.image_univ]
    rw [h1]
    refine (image_closure_subset_closure_image i₁.base.hom.continuous).trans ?_
    rw [Set.image_singleton]
    exact closure_minimal (Set.singleton_subset_iff.mpr h) i₂.isClosedEmbedding.isClosed_range
  intro c
  obtain ⟨c', hc'⟩ := hsub ⟨c, rfl⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) c c' hc'.symm
  exact ⟨z, hz⟩

theorem surjective_snd_of_mem_range {C₁ C₂ Z : Scheme.{u}} [IrreducibleSpace C₂] (i₁ : C₁ ⟶ Z) (i₂ : C₂ ⟶ Z)
    [IsClosedImmersion i₁] (h : i₂.base (genericPoint C₂) ∈ Set.range i₁.base) :
    Function.Surjective (pullback.snd i₁ i₂).base := by
  have hsub : Set.range i₂.base ⊆ Set.range i₁.base := by
    have h1 : Set.range i₂.base = i₂.base '' closure {genericPoint C₂} := by
      rw [genericPoint_closure, Set.image_univ]
    rw [h1]
    refine (image_closure_subset_closure_image i₂.base.hom.continuous).trans ?_
    rw [Set.image_singleton]
    exact closure_minimal (Set.singleton_subset_iff.mpr h) i₁.isClosedEmbedding.isClosed_range
  intro c
  obtain ⟨c', hc'⟩ := hsub ⟨c, rfl⟩
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) c' c hc'
  exact ⟨z, hz⟩

theorem genericPoint_notMem_range_fst {k : Type u} [Field k] {C₁ C₂ Y : Scheme.{u}}
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) [IsIntegral C₁] [SmoothOfRelativeDimension 1 c₁]
    (i₁ : C₁ ⟶ Y) (i₂ : C₂ ⟶ Y) [IsClosedImmersion i₂] [Finite ↥(pullback i₁ i₂)] :
    i₁.base (genericPoint C₁) ∉ Set.range i₂.base := by
  intro h
  have hs := surjective_fst_of_mem_range i₁ i₂ h
  haveI : Finite ↥C₁ := Finite.of_surjective _ hs
  exact (AlgebraicCurve.infinite_setOf_isClosed_singleton c₁) (Set.toFinite _)

theorem genericPoint_notMem_range_snd {k : Type u} [Field k] {C₁ C₂ Y : Scheme.{u}}
    (c₂ : C₂ ⟶ Spec (CommRingCat.of k)) [IsIntegral C₂] [SmoothOfRelativeDimension 1 c₂]
    (i₁ : C₁ ⟶ Y) (i₂ : C₂ ⟶ Y) [IsClosedImmersion i₁] [Finite ↥(pullback i₁ i₂)] :
    i₂.base (genericPoint C₂) ∉ Set.range i₁.base := by
  intro h
  have hs := surjective_snd_of_mem_range i₁ i₂ h
  haveI : Finite ↥C₂ := Finite.of_surjective _ hs
  exact (AlgebraicCurve.infinite_setOf_isClosed_singleton c₂) (Set.toFinite _)

theorem range_mem_irreducibleComponents {C Y : Scheme.{u}} [IrreducibleSpace C] (i : C ⟶ Y) [IsClosedImmersion i]
    (Z : Set Y) (hZ : IsClosed Z) (hcover : ∀ y : Y, y ∈ Set.range i.base ∨ y ∈ Z)
    (hη : i.base (genericPoint C) ∉ Z) :
    Set.range i.base ∈ irreducibleComponents Y := by
  have hirr : IsIrreducible (Set.range i.base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ C).image _ i.base.hom.continuous.continuousOn
  refine ⟨hirr, fun S hS hle => ?_⟩
  have hSsub : S ⊆ Set.range i.base ∪ Z := fun y _ => hcover y
  rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hS.isPreirreducible) _ _
      i.isClosedEmbedding.isClosed_range hZ hSsub with h | h
  · exact h
  · exact absurd (h (hle ⟨genericPoint C, rfl⟩)) hη

theorem genericPoint_eq_of_range {C Y : Scheme.{u}} [IrreducibleSpace C] (i : C ⟶ Y) [IsClosedImmersion i]
    (hZ : IsIrreducible (Set.range i.base)) :
    hZ.genericPoint = i.base (genericPoint C) := by
  have h1 : IsGenericPoint hZ.genericPoint (Set.range i.base) := by
    have := hZ.isGenericPoint_genericPoint_closure
    rwa [i.isClosedEmbedding.isClosed_range.closure_eq] at this
  have h2 : IsGenericPoint (i.base (genericPoint C)) (Set.range i.base) := by
    show closure ({i.base (genericPoint C)} : Set ↥Y) = Set.range i.base
    rw [← Set.image_singleton, i.isClosedEmbedding.closure_image_eq, genericPoint_closure, Set.image_univ]
  exact h1.eq h2

end X1TransvEngine

end

end EngineU

section MainTBS

open IsLocalRing

theorem solution
    {k : Type u} [Field k] {Y C₁ C₂ : Scheme.{u}}
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsIntegral C₁] [SmoothOfRelativeDimension 1 c₁] [IsIntegral C₂] [SmoothOfRelativeDimension 1 c₂]
    (i₁ : C₁ ⟶ Y) (i₂ : C₂ ⟶ Y) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : ∀ z : ↥Y, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    [IsReduced (pullback i₁ i₂)] [Finite ↥(pullback i₁ i₂)] (ν : ↥(pullback i₁ i₂))
    (hk₁ : i₁.base (genericPoint C₁) ⤳ i₁.base ((pullback.fst i₁ i₂).base ν))
    (hy₂ : i₂.base ((pullback.snd i₁ i₂).base ν) = i₁.base ((pullback.fst i₁ i₂).base ν))
    (hk₂ : i₂.base (genericPoint C₂) ⤳ i₁.base ((pullback.fst i₁ i₂).base ν)) :
    RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base ν)).hom = Scheme.branchIdeal hk₁ ∧
    (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base ν)).hom).comap
        (Y.presheaf.stalkSpecializes (specializes_of_eq hy₂)).hom = Scheme.branchIdeal hk₂ ∧
    Scheme.branchIdeal hk₁ ⊔ Scheme.branchIdeal hk₂ =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (i₁.base ((pullback.fst i₁ i₂).base ν))) := by
  classical
  have hne₂ := X1TransvEngine.genericPoint_notMem_range_fst c₁ i₁ i₂
  have hne₁ := X1TransvEngine.genericPoint_notMem_range_snd c₂ i₁ i₂
  have hy₁' : i₁.base (genericPoint C₁) ≠ (i₁.base ((pullback.fst i₁ i₂).base ν)) := fun h => hne₂ ⟨_, hy₂.trans h.symm⟩
  have hy₂' : i₂.base (genericPoint C₂) ≠ (i₁.base ((pullback.fst i₁ i₂).base ν)) := fun h => hne₁ ⟨_, h.symm⟩
  have htri := ECL_Transv.eq_maximalIdeal_or_eq_branchIdeal_or_eq_branchIdeal i₁ i₂ hcover
      (genericPoint C₁) (fun c hc => AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c₁ c hc)
      (genericPoint C₂) (fun c hc => AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c₂ c hc) hk₁ hk₂
  obtain ⟨hPm, hQm, hPQ', hQP'⟩ := ECL_Transv.branchIdeal_ne_maximalIdeal_and_not_le i₁ i₂
      (genericPoint C₁) (fun c hc => AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c₁ c hc)
      (genericPoint C₂) (fun c hc => AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c₂ c hc)
      hk₁ hk₂ hne₁ hne₂ hy₁' hy₂'
  have hJ₁le : RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base ν)).hom ≤ Scheme.branchIdeal hk₁ :=
    TransvChair.ker_stalkMap_le_comap_stalkSpecializes i₁ (genericPoint_specializes _)
  have hJ₂le : (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base ν)).hom).comap
      (Y.presheaf.stalkSpecializes (specializes_of_eq hy₂)).hom ≤
      Scheme.branchIdeal hk₂ := by
    refine (Ideal.comap_mono (TransvChair.ker_stalkMap_le_comap_stalkSpecializes i₂
      (genericPoint_specializes ((pullback.snd i₁ i₂).base ν)))).trans (le_of_eq ?_)
    rw [Ideal.comap_comap, ← CommRingCat.hom_comp, TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  haveI hJ₁p : (RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base ν)).hom).IsPrime := RingHom.ker_isPrime _
  haveI hJ₂p : (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base ν)).hom).IsPrime := RingHom.ker_isPrime _
  haveI hJ₂p' : ((RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base ν)).hom).comap
      (Y.presheaf.stalkSpecializes (specializes_of_eq hy₂)).hom).IsPrime :=
    Ideal.comap_isPrime _ _
  have hJ₁ : RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base ν)).hom = Scheme.branchIdeal hk₁ :=
    ECL_Transv.eq_branchIdeal_of_isPrime_of_le hk₁ hk₂ (fun 𝔮 h𝔮 => htri 𝔮) hPm hQP' _ hJ₁le
  have hJ₂ : (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base ν)).hom).comap
      (Y.presheaf.stalkSpecializes (specializes_of_eq hy₂)).hom = Scheme.branchIdeal hk₂ :=
    ECL_Transv.eq_branchIdeal_of_isPrime_of_le hk₂ hk₁ (fun 𝔮 h𝔮 => (htri 𝔮).imp id Or.symm) hQm hPQ' _ hJ₂le
  have hrad : (Scheme.branchIdeal hk₁ ⊔ Scheme.branchIdeal hk₂).IsRadical :=
    TransvChair.isRadical_sup_of_ker_eq i₁ i₂ ν hy₂ hJ₁ hJ₂
  have hκ : Scheme.branchIdeal hk₁ ⊔ Scheme.branchIdeal hk₂ = IsLocalRing.maximalIdeal _ :=
    eq_of_isRadical_of_le_of_forall_le hrad
      (sup_le (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
        (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)))
      (fun 𝔮 h𝔮 hle => by
        rcases htri 𝔮 with rfl | rfl | rfl
        · exact le_rfl
        · exact absurd (le_sup_right.trans hle) hQP'
        · exact absurd (le_sup_left.trans hle) hPQ')
  exact ⟨hJ₁, hJ₂, hκ⟩

end MainTBS

end S_AlgebraicGeometry_Scheme_ker_stalkMap_eq_branchIdeal_and_branchIdeal_sup_branchIdeal_eq_maximalIdeal_of_isReduced_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_ker_stalkMap_eq_branchIdeal_and_branchIdeal_sup_branchIdeal_eq_maximalIdeal_of_isReduced_pullback (solution)

-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.eq_of_forall_section_comp_eq_of_dense_of_dualNumber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/cba7bc64-826f-54e4-a563-952cf826fd09

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_section_comp_eq_of_dense_of_dualNumber

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

namespace DenseEqEps

open scoped DualNumber

theorem eq_zero_of_forall_algHom {k : Type u} [Field k] [IsAlgClosed k]
    {A : Type u} [CommRing A] [Algebra k A] [IsReduced A] [Algebra.FiniteType k A]
    (U : Set (PrimeSpectrum A)) (hUo : IsOpen U) (hU : Dense U) (a : A)
    (ha : ∀ m : PrimeSpectrum A, m ∈ U → ∀ y : A →ₐ[k] k,
      RingHom.ker (y : A →+* k) = m.asIdeal → y a = 0) : a = 0 := by
  classical
  by_contra h0
  have hna : ¬ IsNilpotent a := fun h => h0 h.eq_zero
  have hD : ((PrimeSpectrum.basicOpen a : TopologicalSpace.Opens (PrimeSpectrum A)) :
      Set (PrimeSpectrum A)).Nonempty := by
    by_contra hne
    apply hna
    rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
    ext x
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => hne ⟨x, hx⟩
  obtain ⟨x, hxa, hxU⟩ := hU.inter_open_nonempty _ (PrimeSpectrum.basicOpen a).isOpen hD
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  obtain ⟨m, ⟨hma, hmU⟩, hmc⟩ := (jacobsonSpace_iff_locallyClosed.mp inferInstance)
    (((PrimeSpectrum.basicOpen a : TopologicalSpace.Opens (PrimeSpectrum A)) : Set (PrimeSpectrum A)) ∩ U)
    ⟨x, hxa, hxU⟩ (((PrimeSpectrum.basicOpen a).isOpen.inter hUo).isLocallyClosed)
  rw [mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal] at hmc
  letI := Ideal.Quotient.field m.asIdeal
  haveI : Module.Finite k (A ⧸ m.asIdeal) := finite_of_finite_type_of_isJacobsonRing k _
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := A ⧸ m.asIdeal)
  let e : k ≃ₐ[k] (A ⧸ m.asIdeal) := AlgEquiv.ofBijective (Algebra.ofId k _) hbij
  let y : A →ₐ[k] k := (e.symm : (A ⧸ m.asIdeal) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m.asIdeal)
  have hy : RingHom.ker (y : A →+* k) = m.asIdeal := by
    ext b
    simp only [RingHom.mem_ker, AlgHom.coe_toRingHom, AlgHom.coe_comp, Function.comp_apply,
      Ideal.Quotient.mkₐ_eq_mk, y, AlgEquiv.coe_algHom, map_eq_zero_iff _ e.symm.injective,
      Ideal.Quotient.eq_zero_iff_mem]
  have h1 := ha m hmU y hy
  apply (PrimeSpectrum.mem_basicOpen _ _).mp hma
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have : e.symm (Ideal.Quotient.mk m.asIdeal a) = 0 := by simpa [y] using h1
  simpa using this

theorem exists_eq_tmul_one_add_tmul_eps {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
    (r : A ⊗[k] k[ε]) : ∃ a₀ a₁ : A, r = a₀ ⊗ₜ[k] (1 : k[ε]) + a₁ ⊗ₜ[k] ε := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a x =>
    refine ⟨x.fst • a, x.snd • a, ?_⟩
    conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
    rw [TensorProduct.tmul_add, DualNumber.inr_eq_smul_eps, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul]
    congr 1
    have : (TrivSqZeroExt.inl x.fst : k[ε]) = x.fst • (1 : k[ε]) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [this, TensorProduct.tmul_smul]
  | add r s hr hs =>
    obtain ⟨a₀, a₁, rfl⟩ := hr
    obtain ⟨b₀, b₁, rfl⟩ := hs
    exact ⟨a₀ + b₀, a₁ + b₁, by simp [TensorProduct.add_tmul]; abel⟩

noncomputable def evalEps {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
    (y : A →ₐ[k] k) : A ⊗[k] k[ε] →ₐ[k] k[ε] :=
  Algebra.TensorProduct.lift ((Algebra.ofId k k[ε]).comp y) (AlgHom.id k k[ε]) (fun _ _ => .all _ _)

theorem evalEps_tmul {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
    (y : A →ₐ[k] k) (a : A) (x : k[ε]) : evalEps y (a ⊗ₜ x) = y a • x := by
  simp [evalEps, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]

theorem tensor_eq_zero_of_forall_evalEps {k : Type u} [Field k] [IsAlgClosed k]
    {A : Type u} [CommRing A] [Algebra k A] [IsReduced A] [Algebra.FiniteType k A]
    (U : Set (PrimeSpectrum A)) (hUo : IsOpen U) (hU : Dense U) (r : A ⊗[k] k[ε])
    (hr : ∀ m : PrimeSpectrum A, m ∈ U → ∀ y : A →ₐ[k] k,
      RingHom.ker (y : A →+* k) = m.asIdeal → evalEps y r = 0) : r = 0 := by
  obtain ⟨a₀, a₁, rfl⟩ := exists_eq_tmul_one_add_tmul_eps r
  have key : ∀ m : PrimeSpectrum A, m ∈ U → ∀ y : A →ₐ[k] k,
      RingHom.ker (y : A →+* k) = m.asIdeal → y a₀ = 0 ∧ y a₁ = 0 := by
    intro m hm y hy
    have h := hr m hm y hy
    rw [map_add, evalEps_tmul, evalEps_tmul] at h
    have h0 := congrArg TrivSqZeroExt.fst h
    have h1 := congrArg TrivSqZeroExt.snd h
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_one,
      DualNumber.fst_eps, smul_eq_mul, mul_one, mul_zero, add_zero, TrivSqZeroExt.fst_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_smul, TrivSqZeroExt.snd_one, DualNumber.snd_eps,
      zero_add, TrivSqZeroExt.snd_zero] at h0 h1
    exact ⟨h0, h1⟩
  have e0 : a₀ = 0 := eq_zero_of_forall_algHom U hUo hU a₀ (fun m hm y hy => (key m hm y hy).1)
  have e1 : a₁ = 0 := eq_zero_of_forall_algHom U hUo hU a₁ (fun m hm y hy => (key m hm y hy).2)
  simp [e0, e1]

open IsLocalRing in

theorem chart {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsReduced X]
    (U : X.Opens) (hU : Dense (U : Set X))
    {A : CommRingCat.{u}} [Algebra k A] [IsReduced A] [Algebra.FiniteType k A]
    (a : Spec A ⟶ X) [IsOpenImmersion a]
    {Z : Scheme.{u}}
    (ι : Z ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k[ε])))) [IsClosedImmersion ι]
    (hι : ∀ y : A →ₐ[k] k,
      (Spec.map (CommRingCat.ofHom (y : A →+* k)) ≫ a).base (closedPoint k) ∈ U →
      ∀ T : Spec (CommRingCat.of k[ε]) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k[ε]))),
        T ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap k k[ε])) ≫
          Spec.map (CommRingCat.ofHom (y : A →+* k)) ≫ a →
        T ≫ pullback.snd f _ = 𝟙 _ → ∃ u : Spec (CommRingCat.of k[ε]) ⟶ Z, u ≫ ι = T)
    (g : Spec (CommRingCat.of (A ⊗[k] k[ε])) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k[ε])))) [IsOpenImmersion g]
    (hg1 : g ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[k] k[ε]))) ≫ a)
    (hg2 : g ≫ pullback.snd f _ = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := k[ε])).toRingHom)) :
    ι.ker.ideal ⟨g ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion g⟩ = ⊥ := by
  classical
  have H := IsPullback.of_hasPullback g ι
  have hker := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion ι (pullback.fst g ι)
    (pullback.snd g ι) g H ⟨⊤, isAffineOpen_top _⟩
  suffices h : (pullback.fst g ι).ker.ideal ⟨⊤, isAffineOpen_top _⟩ = ⊥ by
    rw [hker] at h
    have hsurj : Function.Surjective (g.appIso ⊤).inv.hom :=
      (ConcreteCategory.bijective_of_isIso (g.appIso ⊤).inv).2
    have e := Ideal.map_comap_of_surjective (g.appIso ⊤).inv.hom hsurj
      (ι.ker.ideal ⟨g ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion g⟩)
    rw [← e, h, Ideal.map_bot]
  rw [Scheme.Hom.ker_apply, eq_bot_iff]
  intro s hs
  rw [RingHom.mem_ker] at hs
  obtain ⟨r, rfl⟩ : ∃ r, s = (Scheme.ΓSpecIso (.of (A ⊗[k] k[ε]))).inv r :=
    ⟨(Scheme.ΓSpecIso (.of (A ⊗[k] k[ε]))).hom s, by simp⟩
  suffices hr : r = 0 by simp [hr]
  refine tensor_eq_zero_of_forall_evalEps (k := k) (A := A) (a.base ⁻¹' (U : Set X))
    (U.isOpen.preimage a.continuous) (hU.preimage a.isOpenEmbedding.isOpenMap) r ?_
  intro m hm y hy

  let ψ : A ⊗[k] k[ε] →+* k[ε] := (evalEps y).toRingHom
  have hψ : ∀ z, ψ z = evalEps y z := fun _ => rfl
  set t : Spec (CommRingCat.of k[ε]) ⟶ Spec (CommRingCat.of (A ⊗[k] k[ε])) :=
    Spec.map (CommRingCat.ofHom (R := A ⊗[k] k[ε]) (S := k[ε]) ψ) with ht
  have ht1 : (t ≫ g) ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap k k[ε])) ≫
      Spec.map (CommRingCat.ofHom (y : A →+* k)) ≫ a := by
    rw [Category.assoc, hg1, ← Category.assoc, ← Category.assoc, ht, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
    refine RingHom.ext fun x => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, hψ, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, evalEps_tmul, AlgHom.coe_toRingHom]
    rw [Algebra.algebraMap_eq_smul_one]
  have ht2 : (t ≫ g) ≫ pullback.snd f _ = 𝟙 _ := by
    rw [Category.assoc, hg2, ht, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_id]
    congr 1
    refine RingHom.ext fun x => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, hψ, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply, evalEps_tmul, map_one,
      one_smul, RingHom.id_apply]
  have hpt : (Spec.map (CommRingCat.ofHom (y : A →+* k)) ≫ a).base (closedPoint k) ∈ U := by
    have : (Spec.map (CommRingCat.ofHom (y : A →+* k))).base (closedPoint k) = m := by
      apply PrimeSpectrum.ext
      change Ideal.comap (CommRingCat.ofHom (y : A →+* k)).hom (maximalIdeal k) = m.asIdeal
      rw [CommRingCat.hom_ofHom, maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hy]
    show (Spec.map (CommRingCat.ofHom (y : A →+* k)) ≫ a) (closedPoint k) ∈ U
    rw [Scheme.Hom.comp_apply]
    change a.base ((Spec.map (CommRingCat.ofHom (y : A →+* k))).base (closedPoint k)) ∈ (U : Set X)
    rw [this]
    exact hm
  obtain ⟨u, hu⟩ := hι y hpt (t ≫ g) ht1 ht2
  let v : Spec (CommRingCat.of k[ε]) ⟶ pullback g ι := pullback.lift t u hu.symm
  have hv : v ≫ pullback.fst g ι = t := pullback.lift_fst _ _ _
  have h0 : t.appTop ((Scheme.ΓSpecIso (.of (A ⊗[k] k[ε]))).inv r) = 0 := by
    have hs' : (pullback.fst g ι).appTop ((Scheme.ΓSpecIso (.of (A ⊗[k] k[ε]))).inv r) = 0 := hs
    rw [← hv, Scheme.Hom.comp_appTop]
    change v.appTop ((pullback.fst g ι).appTop _) = 0
    rw [hs', map_zero]
  have nat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (R := A ⊗[k] k[ε]) (S := k[ε]) ψ)
  have h1 : (Scheme.ΓSpecIso (.of k[ε])).inv (evalEps y r) = 0 := by
    have e1 := congrArg (fun φ => φ.hom r) nat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e1
    rw [← ht, hψ] at e1
    erw [e1]
    exact h0
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of k[ε])).inv).1).mp h1

theorem main
    (k : Type u) [Field k] [IsAlgClosed k] {X Y S : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsReduced X] [LocallyOfFiniteType f]
    (F G : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) ⟶ Y)
    (i : Y ⟶ S) [IsSeparated i] (hFG : F ≫ i = G ≫ i)
    (U : X.Opens) (hU : Dense (U : Set ↥X))
    (h : ∀ (y : Spec (CommRingCat.of k) ⟶ X), y ≫ f = 𝟙 _ → y.base (IsLocalRing.closedPoint k) ∈ U →
      ∀ (T : Spec (CommRingCat.of (DualNumber k)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))),
        T ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ y →
        T ≫ pullback.snd f _ = 𝟙 _ → T ≫ F = T ≫ G) :
    F = G := by
  classical

  let X' : Over S := Over.mk (F ≫ i)
  let Y' : Over S := Over.mk i
  let F' : X' ⟶ Y' := Over.homMk F rfl
  let G' : X' ⟶ Y' := Over.homMk G (by exact hFG.symm)
  haveI : IsSeparated Y'.hom := ‹IsSeparated i›
  let ι : (equalizer F' G').left ⟶ pullback f _ := (equalizer.ι F' G').left
  haveI hιc : IsClosedImmersion ι := AlgebraicGeometry.isClosedImmersion_equalizer_ι_left F' G'
  suffices IsIso ι by
    have hc := congr($(equalizer.condition F' G').left)
    simp only [Over.comp_left, Over.homMk_left, F', G'] at hc
    rw [← cancel_epi ι]
    exact hc
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  have hfac : ∀ {W : Scheme.{u}}
      (T : W ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))),
      T ≫ F = T ≫ G → ∃ u : W ⟶ (equalizer F' G').left, u ≫ ι = T := by
    intro W T hT
    let W' : Over S := Over.mk (T ≫ F ≫ i)
    let T' : W' ⟶ X' := Over.homMk T rfl
    have hT' : T' ≫ F' = T' ≫ G' := by ext; (simp [Over.comp_left, Over.homMk_left] at hT ⊢; exact hT)
    refine ⟨(equalizer.lift T' hT').left, ?_⟩
    have := congr($(equalizer.lift_ι T' hT').left)
    simp only [Over.comp_left, Over.homMk_left] at this
    exact this

  let 𝒰 := X.affineOpenCover
  letI inst : ∀ j : 𝒰.I₀, Algebra k (𝒰.X j) := fun j => (Spec.preimage (𝒰.f j ≫ f)).hom.toAlgebra
  have hspec : ∀ j, 𝒰.f j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (𝒰.X j))) := fun j => by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  let 𝒱₀ := Scheme.Pullback.openCoverOfLeft 𝒰.openCover f
    (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
  let e₂ : ∀ j : 𝒰.I₀, Spec (CommRingCat.of ((𝒰.X j) ⊗[k] k[ε])) ≅
      pullback (𝒰.f j ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) := fun j =>
    (pullbackSpecIso k (𝒰.X j) k[ε]).symm ≪≫ pullback.congrHom (hspec j).symm rfl
  have he1 : ∀ j, (e₂ j).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap (𝒰.X j) ((𝒰.X j) ⊗[k] k[ε]))) := by
    intro j
    simp only [e₂, Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc]
    erw [pullback.lift_fst]
    rw [Category.comp_id, pullbackSpecIso_inv_fst']
  have he2 : ∀ j, (e₂ j).hom ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := k) (A := 𝒰.X j) (B := k[ε])).toRingHom) := by
    intro j
    simp only [e₂, Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc]
    erw [pullback.lift_snd]
    rw [Category.comp_id, pullbackSpecIso_inv_snd]
    rfl
  have hf1 : ∀ j, 𝒱₀.f j ≫ pullback.fst f _ = pullback.fst _ _ ≫ 𝒰.f j := by
    intro j
    show (Scheme.Pullback.openCoverOfLeft 𝒰.openCover f _).f j ≫ _ = _
    rw [Scheme.Pullback.openCoverOfLeft_f]
    exact pullback.lift_fst _ _ _
  have hf2 : ∀ j, 𝒱₀.f j ≫ pullback.snd f _ = pullback.snd _ _ := by
    intro j
    show (Scheme.Pullback.openCoverOfLeft 𝒰.openCover f _).f j ≫ _ = _
    rw [Scheme.Pullback.openCoverOfLeft_f]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  let 𝒱 : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))).OpenCover :=
    𝒱₀.copy 𝒰.I₀ (fun j => Spec (CommRingCat.of ((𝒰.X j) ⊗[k] k[ε])))
    (fun j => (e₂ j).hom ≫ 𝒱₀.f j) (Equiv.refl _) e₂ (fun _ => rfl)
  have hVf : ∀ j, 𝒱.f j = (e₂ j).hom ≫ 𝒱₀.f j := fun _ => rfl
  have hg1 : ∀ j, ((e₂ j).hom ≫ 𝒱₀.f j) ≫ pullback.fst f _ =
      Spec.map (CommRingCat.ofHom (algebraMap (𝒰.X j) ((𝒰.X j) ⊗[k] k[ε]))) ≫ 𝒰.f j := by
    intro j
    rw [Category.assoc]
    erw [hf1 j]
    erw [← Category.assoc, he1 j]
  have hg2 : ∀ j, ((e₂ j).hom ≫ 𝒱₀.f j) ≫ pullback.snd f _ = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := k) (A := 𝒰.X j) (B := k[ε])).toRingHom) := by
    intro j
    rw [Category.assoc]
    erw [hf2 j]
    erw [he2 j]
  haveI hVaff : ∀ j, IsAffine (𝒱.X j) := fun j =>
    (inferInstance : IsAffine (Spec (CommRingCat.of ((𝒰.X j) ⊗[k] k[ε]))))
  haveI hVopen : ∀ j, IsOpenImmersion ((e₂ j).hom ≫ 𝒱₀.f j) := fun j =>
    (inferInstance : IsOpenImmersion (𝒱.f j))
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun j => ⟨𝒱.f j ''ᵁ ⊤, (isAffineOpen_top (𝒱.X j)).image_of_isOpenImmersion (𝒱.f j)⟩) ?_ ?_
  · show ⨆ j, 𝒱.f j ''ᵁ ⊤ = ⊤
    simp only [Scheme.Hom.image_top_eq_opensRange]
    exact 𝒱.iSup_opensRange
  intro j
  rw [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  haveI : IsReduced (𝒰.X j) := by
    have : IsReduced (Spec (𝒰.X j)) := isReduced_of_isOpenImmersion (𝒰.f j)
    exact (affine_isReduced_iff (𝒰.X j)).mp this
  haveI : Algebra.FiniteType k (𝒰.X j) := by
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k (𝒰.X j)))) := by
      rw [← hspec j]; infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at this
    exact RingHom.finiteType_algebraMap.mp this
  show ι.ker.ideal ⟨((e₂ j).hom ≫ 𝒱₀.f j) ''ᵁ ⊤, _⟩ = ⊥
  refine chart f U hU (A := 𝒰.X j) (a := 𝒰.f j) ι ?_ ((e₂ j).hom ≫ 𝒱₀.f j) (hg1 j) (hg2 j)
  intro y hy T hT1 hT2
  refine hfac T (h _ ?_ hy T hT1 hT2)
  rw [Category.assoc, hspec j, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_id]
  congr 1
  exact y.comp_algebraMap

end DenseEqEps

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X Y S : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsReduced X] [LocallyOfFiniteType f]
    (F G : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) ⟶ Y)
    (i : Y ⟶ S) [IsSeparated i] (hFG : F ≫ i = G ≫ i)
    (U : X.Opens) (hU : Dense (U : Set ↥X))
    (h : ∀ (y : Spec (CommRingCat.of k) ⟶ X), y ≫ f = 𝟙 _ → y.base (IsLocalRing.closedPoint k) ∈ U →
      ∀ (T : Spec (CommRingCat.of (DualNumber k)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))),
        T ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ y →
        T ≫ pullback.snd f _ = 𝟙 _ → T ≫ F = T ≫ G) :
    F = G := by
  exact DenseEqEps.main k f F G i hFG U hU h

end S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_section_comp_eq_of_dense_of_dualNumber
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_section_comp_eq_of_dense_of_dualNumber (solution)

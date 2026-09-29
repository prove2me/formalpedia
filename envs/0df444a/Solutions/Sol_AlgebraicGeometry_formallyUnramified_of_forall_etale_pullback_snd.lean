-- Prove2me | solution 1 for AlgebraicGeometry.formallyUnramified_of_forall_etale_pullback_snd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/864459b7-e9f6-53bb-a34e-e2b9de0cbcf4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_formallyUnramified_of_forall_etale_pullback_snd

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace UHost

p2m_open "Algebra CategoryTheory.Algebra"

theorem formallyUnramified_of_forall_isMaximal {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [EssFiniteType R A] (h : ∀ (n : Ideal A) [n.IsMaximal], IsUnramifiedAt R n) :
    FormallyUnramified R A := by
  rw [formallyUnramified_iff_forall]
  intro q
  by_contra hq
  obtain ⟨n, hn, hqn⟩ := Ideal.exists_le_maximal q.asIdeal q.2.ne_top
  let n' : PrimeSpectrum A := ⟨n, hn.isPrime⟩
  have hcl : IsClosed (unramifiedLocus R A)ᶜ := (isOpen_unramifiedLocus (R := R) (A := A)).isClosed_compl
  have hmem : n' ∈ (unramifiedLocus R A)ᶜ := by
    have : n' ∈ closure {q} := (PrimeSpectrum.le_iff_mem_closure q n').mp hqn
    exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hq) this
  exact hmem (@h n hn)

theorem isUnramifiedAt_of_map_eq_maximalIdeal {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [EssFiniteType R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)] [Localization.AtPrime.IsLiesOverAlgebra p q]
    (hsep : Algebra.IsSeparable p.ResidueField q.ResidueField)
    (hmap : p.map (algebraMap R (Localization.AtPrime q)) = IsLocalRing.maximalIdeal _) :
    IsUnramifiedAt R q :=
  (Algebra.isUnramifiedAt_iff_map_eq R p q).mpr ⟨hsep, hmap⟩

end UHost

namespace UHost

p2m_open "Algebra CategoryTheory.Algebra IsLocalRing"

theorem exists_mul_eq_zero_of_formallyUnramified_field {K P : Type u} [Field K] [CommRing P]
    [Algebra K P] [FormallyUnramified K P] [EssFiniteType K P] (m : Ideal P) [hm : m.IsMaximal]
    (x : P) (hx : x ∈ m) : ∃ t ∉ m, t * x = 0 := by
  let Pm := Localization.AtPrime m
  haveI : FormallyUnramified K Pm := FormallyUnramified.comp K P Pm
  haveI : EssFiniteType K Pm := EssFiniteType.comp K P Pm
  haveI : IsLocalHom (algebraMap K Pm) := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have : a = 0 := by simpa using h
    rw [this, map_zero] at ha
    exact not_isUnit_zero ha
  have hmap := FormallyUnramified.map_maximalIdeal (R := K) (S := Pm)
  rw [maximalIdeal_eq_bot (R := K), Ideal.map_bot] at hmap

  have hxm : algebraMap P Pm x ∈ maximalIdeal Pm := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hx
  rw [← hmap, Ideal.mem_bot, IsLocalization.map_eq_zero_iff m.primeCompl] at hxm
  obtain ⟨t, ht⟩ := hxm
  exact ⟨t.1, t.2, ht⟩

theorem map_eq_maximalIdeal_of_forall_exists {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (p : Ideal R) (n : Ideal A) [hn : n.IsPrime] (hpn : p ≤ n.comap (algebraMap R A))
    (h : ∀ x ∈ n, ∃ t ∉ n, t * x ∈ p.map (algebraMap R A)) :
    p.map (algebraMap R (Localization.AtPrime n)) = maximalIdeal (Localization.AtPrime n) := by
  apply le_antisymm
  · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply R A (Localization.AtPrime n)]
    exact Ideal.mem_map_of_mem _ (hpn hr)
  · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨t, htn, htx⟩ := h x hx
    rw [Ideal.mem_comap]
    have h1 : algebraMap A (Localization.AtPrime n) (t * x) ∈ p.map (algebraMap R (Localization.AtPrime n)) := by
      rw [IsScalarTower.algebraMap_eq R A (Localization.AtPrime n), ← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ htx
    rw [map_mul] at h1
    have hu : IsUnit (algebraMap A (Localization.AtPrime n) t) :=
      IsLocalization.map_units (Localization.AtPrime n) (⟨t, show t ∈ n.primeCompl from htn⟩ : n.primeCompl)
    have := Ideal.mul_mem_left _ (hu.unit⁻¹ : (Localization.AtPrime n)ˣ).1 h1
    rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at this

end UHost

namespace UHost

p2m_open "Algebra CategoryTheory.Algebra IsLocalRing"

theorem isSeparable_residueField_of_isAlgClosed {k R A : Type u} [Field k] [IsAlgClosed k]
    [CommRing R] [CommRing A] [Algebra k R] [Algebra k A] [Algebra R A] [IsScalarTower k R A]
    [Algebra.FiniteType k A] (n : Ideal A) [hn : n.IsMaximal] (p : Ideal R) [p.IsPrime] [n.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime n)] [Localization.AtPrime.IsLiesOverAlgebra p n] :
    Algebra.IsSeparable p.ResidueField n.ResidueField := by

  letI : Field (A ⧸ n) := Ideal.Quotient.field n
  haveI : Module.Finite k (A ⧸ n) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ n)
  haveI : Algebra.IsIntegral k (A ⧸ n) := Algebra.IsIntegral.of_finite k (A ⧸ n)
  have hk : Function.Surjective (algebraMap k (A ⧸ n)) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := A ⧸ n)).2
  have hsurj : Function.Surjective (algebraMap p.ResidueField n.ResidueField) := by
    intro z
    obtain ⟨y, rfl⟩ := (Ideal.bijective_algebraMap_quotient_residueField n).2 z
    obtain ⟨c, rfl⟩ := hk y
    refine ⟨algebraMap R p.ResidueField (algebraMap k R c), ?_⟩
    rw [← IsScalarTower.algebraMap_apply R p.ResidueField n.ResidueField,
      IsScalarTower.algebraMap_apply R A n.ResidueField, ← IsScalarTower.algebraMap_apply k R A,
      IsScalarTower.algebraMap_apply k A (A ⧸ n), IsScalarTower.algebraMap_apply A (A ⧸ n) n.ResidueField]
  exact ⟨fun z => by obtain ⟨c, rfl⟩ := hsurj z; exact isSeparable_algebraMap c⟩

theorem isUnramifiedAt_of_fibre {k R A P K : Type u} [Field k] [IsAlgClosed k] [CommRing R] [CommRing A]
    [CommRing P] [Field K] [Algebra k R] [Algebra k A] [Algebra R A] [IsScalarTower k R A]
    [Algebra.FiniteType k A] [EssFiniteType R A] [Algebra K P] [FormallyUnramified K P] [EssFiniteType K P]
    (n : Ideal A) [hn : n.IsMaximal] (p : Ideal R) [p.IsPrime] [n.LiesOver p]
    (a : A →+* P) (ha : Function.Surjective a) (hker : RingHom.ker a ≤ p.map (algebraMap R A)) :
    IsUnramifiedAt R n := by

  have hkn : RingHom.ker a ≤ n := by
    refine hker.trans ?_
    rw [Ideal.map_le_iff_le_comap]
    exact (Ideal.LiesOver.over (P := n) (p := p)).le
  have hcm : (n.map a).comap a = n := by
    rw [Ideal.comap_map_of_surjective a ha, sup_eq_left, ← RingHom.ker_eq_comap_bot]
    exact hkn
  have hmn : (n.map a).IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective a ha hn with h | h
    · exfalso
      apply hn.ne_top
      rw [← hcm, h, Ideal.comap_top]
    · exact h

  have hfib : ∀ x ∈ n, ∃ t ∉ n, t * x ∈ p.map (algebraMap R A) := by
    intro x hx
    haveI := hmn
    obtain ⟨t', ht'm, ht'x⟩ :=
      exists_mul_eq_zero_of_formallyUnramified_field (K := K) (n.map a) (a x) (Ideal.mem_map_of_mem a hx)
    obtain ⟨t, rfl⟩ := ha t'
    refine ⟨t, fun htn => ht'm (Ideal.mem_map_of_mem a htn), hker ?_⟩
    rw [RingHom.mem_ker, map_mul, ht'x]
  have hmap := map_eq_maximalIdeal_of_forall_exists p n
    (Ideal.LiesOver.over (P := n) (p := p)).le hfib
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime n) := Localization.AtPrime.algebraOfLiesOver p n
  exact isUnramifiedAt_of_map_eq_maximalIdeal p n (isSeparable_residueField_of_isAlgClosed (k := k) n p) hmap

end UHost

namespace UHost

p2m_open "Algebra CategoryTheory.Algebra"

theorem surjective_and_ker_of_isPushout_of_surjective {A B C P : CommRingCat.{u}}
    {f : A ⟶ C} {g : A ⟶ B} {inl : C ⟶ P} {inr : B ⟶ P}
    (h : IsPushout f g inl inr) (hg : Function.Surjective g.hom) :
    Function.Surjective inl.hom ∧ RingHom.ker inl.hom = (RingHom.ker g.hom).map f.hom := by
  have hw : ∀ a, inl.hom (f.hom a) = inr.hom (g.hom a) := fun a => by
    have := congrArg (fun k => k.hom a) h.w
    simpa using this
  constructor
  · let S : Subring P := inl.hom.range
    have hinrS : ∀ b, inr.hom b ∈ S := fun b => by
      obtain ⟨a, rfl⟩ := hg b
      exact ⟨f.hom a, hw a⟩
    let i₁ : C ⟶ CommRingCat.of S := CommRingCat.ofHom inl.hom.rangeRestrict
    let i₂ : B ⟶ CommRingCat.of S := CommRingCat.ofHom (inr.hom.codRestrict S hinrS)
    have hcomm : f ≫ i₁ = g ≫ i₂ := by
      ext a
      exact hw a
    let u : P ⟶ CommRingCat.of S := h.desc i₁ i₂ hcomm
    let val : CommRingCat.of S ⟶ P := CommRingCat.ofHom S.subtype
    have h1 : inl ≫ (u ≫ val) = inl := by
      rw [← Category.assoc, h.inl_desc]; rfl
    have h2 : inr ≫ (u ≫ val) = inr := by
      rw [← Category.assoc, h.inr_desc]; rfl
    have huv : u ≫ val = 𝟙 P := h.hom_ext (by rw [h1, Category.comp_id]) (by rw [h2, Category.comp_id])
    intro p
    have : val.hom (u.hom p) = p := by
      have := congrArg (fun k => k.hom p) huv
      simpa using this
    obtain ⟨c, hc⟩ := (u.hom p).2
    exact ⟨c, hc.trans this⟩
  · apply le_antisymm
    · set K : Ideal C := (RingHom.ker g.hom).map f.hom with hK
      let e : (A ⧸ RingHom.ker g.hom) ≃+* B := RingHom.quotientKerEquivOfSurjective hg
      let j₁ : C ⟶ CommRingCat.of (C ⧸ K) := CommRingCat.ofHom (Ideal.Quotient.mk K)
      let l : (A ⧸ RingHom.ker g.hom) →+* C ⧸ K :=
        Ideal.Quotient.lift (RingHom.ker g.hom) ((Ideal.Quotient.mk K).comp f.hom) (fun a ha => by
          rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hK]
          exact Ideal.mem_map_of_mem _ ha)
      let j₂ : B ⟶ CommRingCat.of (C ⧸ K) := CommRingCat.ofHom (l.comp e.symm.toRingHom)
      have hcomm : f ≫ j₁ = g ≫ j₂ := by
        ext a
        show Ideal.Quotient.mk K (f.hom a) = l (e.symm (g.hom a))
        have : e.symm (g.hom a) = Ideal.Quotient.mk _ a := by
          apply e.injective
          rw [RingEquiv.apply_symm_apply]
          rfl
        rw [this]
        rfl
      intro c hc
      have := congrArg (fun k => k.hom c) (h.inl_desc j₁ j₂ hcomm)
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
      rw [RingHom.mem_ker] at hc
      rw [hc, map_zero] at this
      have : Ideal.Quotient.mk K c = 0 := by
        rw [eq_comm] at this
        exact this
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, hw a, RingHom.mem_ker.mp ha, map_zero]

theorem appLE_fromSpec_top {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (h : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  have : ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE h).op :
      Opposite.op (⊤ : (Spec Γ(X, U)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id, Category.comp_id]

theorem appLE_top_top' {X Y : Scheme.{u}} (f : X ⟶ Y) (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ h = f.appTop := (Scheme.Hom.app_eq_appLE f).symm

theorem appLE_SpecMap_comp_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {K : CommRingCat.{u}} (ψ : Γ(X, U) ⟶ K) (h : (⊤ : (Spec K).Opens) ≤ (Spec.map ψ ≫ hU.fromSpec) ⁻¹ᵁ U) :
    (Spec.map ψ ≫ hU.fromSpec).appLE U ⊤ h = ψ ≫ (Scheme.ΓSpecIso K).inv := by
  have h1 : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U := by
    rw [hU.fromSpec_preimage_self]
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map ψ) hU.fromSpec U ⊤ ⊤ h1 le_top, appLE_fromSpec_top hU h1,
    appLE_top_top', Scheme.ΓSpecIso_inv_naturality]

theorem SpecMap_comp_fromSpec_comp {Y : Scheme.{u}} {U : Y.Opens} (hU : IsAffineOpen U)
    {K : CommRingCat.{u}} (ψ : Γ(Y, U) ⟶ K) {L : CommRingCat.{u}} (g : Y ⟶ Spec L) :
    Spec.map ψ ≫ hU.fromSpec ≫ g = Spec.map ((Scheme.ΓSpecIso L).inv ≫ g.appLE ⊤ U le_top ≫ ψ) := by
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top (Spec L)) hU le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h1
  rw [← h1, Spec.map_comp, Spec.map_comp, Category.assoc]

theorem exists_algHom_ker_eq {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (n : Ideal A) [hn : n.IsMaximal] :
    ∃ χ : A →ₐ[k] k, RingHom.ker χ.toRingHom = n := by
  letI : Field (A ⧸ n) := Ideal.Quotient.field n
  haveI : Module.Finite k (A ⧸ n) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ n)
  haveI : Algebra.IsIntegral k (A ⧸ n) := Algebra.IsIntegral.of_finite k (A ⧸ n)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := A ⧸ n)
  let e : k ≃ₐ[k] (A ⧸ n) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ n)) hb
  refine ⟨(e.symm : (A ⧸ n) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k n), ?_⟩
  ext x
  rw [RingHom.mem_ker]
  show e.symm (Ideal.Quotient.mk n x) = 0 ↔ x ∈ n
  rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

end UHost

namespace UHost

p2m_open "Algebra CategoryTheory.Algebra"

theorem formallyUnramified_main
    (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (φ : X ⟶ Y) (hφ : φ ≫ g = f)
    (het : ∀ (y : Spec (CommRingCat.of k) ⟶ Y), y ≫ g = 𝟙 _ → Etale (pullback.snd φ y)) :
    FormallyUnramified φ := by
  haveI : LocallyOfFiniteType φ := by
    have : LocallyOfFiniteType (φ ≫ g) := by rw [hφ]; infer_instance
    exact locallyOfFiniteType_of_comp φ g
  rw [HasRingHomProperty.iff_appLE (P := @FormallyUnramified)]
  intro U V e
  have hU : IsAffineOpen U.1 := U.2
  have hV : IsAffineOpen V.1 := V.2

  set φUV : Γ(Y, U.1) ⟶ Γ(X, V.1) := φ.appLE U.1 V.1 e with hφUV
  let ρY : CommRingCat.of k ⟶ Γ(Y, U.1) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appLE ⊤ U.1 le_top
  let ρX : CommRingCat.of k ⟶ Γ(X, V.1) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V.1 le_top
  have hρ : ρY ≫ φUV = ρX := by
    simp only [ρY, ρX, hφUV, Category.assoc, Scheme.Hom.appLE_comp_appLE, hφ]
  letI iRA : Algebra Γ(Y, U.1) Γ(X, V.1) := φUV.hom.toAlgebra
  letI ikR : Algebra k Γ(Y, U.1) := ρY.hom.toAlgebra
  letI ikA : Algebra k Γ(X, V.1) := ρX.hom.toAlgebra
  have hρc : ∀ c : k, φUV.hom (ρY.hom c) = ρX.hom c := fun c => by
    rw [← hρ]; rfl
  haveI : IsScalarTower k Γ(Y, U.1) Γ(X, V.1) := IsScalarTower.of_algebraMap_eq (fun c => (hρc c).symm)
  haveI : Algebra.FiniteType k Γ(X, V.1) := by
    have h1 : (f.appLE ⊤ V.1 le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance ⟨⊤, isAffineOpen_top _⟩ V le_top
    have h2 : ρX.hom.FiniteType :=
      (RingHom.finiteType_respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv
        (f.appLE ⊤ V.1 le_top)).mpr h1
    exact h2
  haveI : Algebra.EssFiniteType Γ(Y, U.1) Γ(X, V.1) := by
    haveI : Algebra.FiniteType Γ(Y, U.1) Γ(X, V.1) :=
      HasRingHomProperty.appLE @LocallyOfFiniteType φ inferInstance U V e
    infer_instance
  change Algebra.FormallyUnramified Γ(Y, U.1) Γ(X, V.1)
  apply formallyUnramified_of_forall_isMaximal
  intro n hn

  obtain ⟨χ, hχ⟩ := exists_algHom_ker_eq (k := k) n
  let ψ : Γ(Y, U.1) ⟶ CommRingCat.of k := CommRingCat.ofHom (χ.toRingHom.comp φUV.hom)
  have hψapp : ∀ r, ψ.hom r = χ (φUV.hom r) := fun r => rfl
  have hψk : ∀ c : k, ψ.hom (ρY.hom c) = c := fun c => by
    rw [hψapp, hρc]; exact χ.commutes c
  have hψk' : ρY ≫ ψ = 𝟙 _ := by
    ext c; exact hψk c
  let y : Spec (CommRingCat.of k) ⟶ Y := Spec.map ψ ≫ hU.fromSpec
  have hy : y ≫ g = 𝟙 _ := by
    show (Spec.map ψ ≫ hU.fromSpec) ≫ g = 𝟙 _
    rw [Category.assoc, SpecMap_comp_fromSpec_comp hU ψ g]
    rw [show (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appLE ⊤ U.1 le_top ≫ ψ = 𝟙 _ from by
      rw [← Category.assoc]; exact hψk']
    exact Spec.map_id _
  have hyU : (⊤ : (Spec (CommRingCat.of k)).Opens) ≤ y ⁻¹ᵁ U.1 := by
    intro z _
    show hU.fromSpec ((Spec.map ψ) z) ∈ (U.1 : Set Y)
    rw [← hU.range_fromSpec]
    exact ⟨_, rfl⟩

  have hEt : Etale (pullback.snd φ y) := het y hy
  have H : IsPullback (pullback.fst φ y) (pullback.snd φ y) φ y := IsPullback.of_hasPullback φ y
  set W : (pullback φ y).Opens := pullback.fst φ y ⁻¹ᵁ V.1 ⊓ pullback.snd φ y ⁻¹ᵁ ⊤ with hW
  have hWV : W ≤ pullback.fst φ y ⁻¹ᵁ V.1 := by rw [hW]; exact inf_le_left
  have hWT : W ≤ pullback.snd φ y ⁻¹ᵁ ⊤ := le_top
  have PO : IsPushout (φ.appLE U.1 V.1 e) (y.appLE U.1 ⊤ hyU)
      ((pullback.fst φ y).appLE V.1 W hWV)
      ((pullback.snd φ y).appLE ⊤ W hWT) :=
    (isIso_pushoutSection_iff H (US := U.1) (UT := ⊤) (UX := V.1) hyU e (UY := W) hW).mp
      (isIso_pushoutSection_of_isAffineOpen H hyU e hW hU (isAffineOpen_top _) hV)
  have hWaff : IsAffineOpen W := by
    have : IsAffine (U.1 : Scheme.{u}) := hU
    have : IsAffine (V.1 : Scheme.{u}) := hV
    have : IsAffine ((⊤ : (Spec (CommRingCat.of k)).Opens) : Scheme.{u}) := isAffineOpen_top _
    exact .of_isIso (Scheme.Hom.isPullback_resLE H hyU e hW).isoPullback.hom

  have hyapp : y.appLE U.1 ⊤ hyU = ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).inv :=
    appLE_SpecMap_comp_fromSpec hU ψ hyU
  have hΓinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.injective
  have hΓsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective
  have hysurj : Function.Surjective (y.appLE U.1 ⊤ hyU).hom := by
    rw [hyapp, CommRingCat.hom_comp]
    refine hΓsurj.comp fun c => ⟨ρY.hom c, hψk c⟩
  have hyker : RingHom.ker (y.appLE U.1 ⊤ hyU).hom ≤ n.under Γ(Y, U.1) := by
    intro r hr
    rw [hyapp, CommRingCat.hom_comp, RingHom.mem_ker, RingHom.comp_apply] at hr
    have h0 : ψ.hom r = 0 := hΓinj (by rw [hr, map_zero])
    rw [hψapp] at h0
    rw [Ideal.under_def, Ideal.mem_comap, ← hχ, RingHom.mem_ker]
    exact h0
  obtain ⟨hasurj, haker⟩ := surjective_and_ker_of_isPushout_of_surjective PO hysurj

  set sW : Γ(Spec (CommRingCat.of k), ⊤) ⟶ Γ(pullback φ y, W) :=
    (pullback.snd φ y).appLE ⊤ W hWT with hsW
  have hEtW : sW.hom.Etale :=
    HasRingHomProperty.appLE @Etale (pullback.snd φ y) hEt ⟨⊤, isAffineOpen_top _⟩ ⟨W, hWaff⟩ hWT
  let κP : CommRingCat.of k ⟶ Γ(pullback φ y, W) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ sW
  letI ikP : Algebra k Γ(pullback φ y, W) := κP.hom.toAlgebra
  haveI : Algebra.FormallyUnramified k Γ(pullback φ y, W) := by
    have h1 : sW.hom.FormallyUnramified := by
      letI := sW.hom.toAlgebra
      haveI : Algebra.Etale Γ(Spec (CommRingCat.of k), ⊤) Γ(pullback φ y, W) := hEtW
      exact (inferInstance : Algebra.FormallyUnramified Γ(Spec (CommRingCat.of k), ⊤) Γ(pullback φ y, W))
    exact (RingHom.FormallyUnramified.respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv sW).mpr h1
  haveI : Algebra.EssFiniteType k Γ(pullback φ y, W) := by
    have h1 : sW.hom.FiniteType := by
      letI := sW.hom.toAlgebra
      haveI : Algebra.Etale Γ(Spec (CommRingCat.of k), ⊤) Γ(pullback φ y, W) := hEtW
      exact (inferInstance : Algebra.FiniteType Γ(Spec (CommRingCat.of k), ⊤) Γ(pullback φ y, W))
    haveI : Algebra.FiniteType k Γ(pullback φ y, W) :=
      (RingHom.finiteType_respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv sW).mpr h1
    infer_instance
  refine isUnramifiedAt_of_fibre (k := k) (K := k) n (n.under Γ(Y, U.1))
    ((pullback.fst φ y).appLE V.1 W hWV).hom hasurj ?_
  rw [haker]
  exact Ideal.map_mono hyker

end UHost

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (φ : X ⟶ Y) (hφ : φ ≫ g = f)
    (het : ∀ (y : Spec (CommRingCat.of k) ⟶ Y), y ≫ g = 𝟙 _ → Etale (pullback.snd φ y)) :
    FormallyUnramified φ :=
  UHost.formallyUnramified_main k f g φ hφ het

end S_AlgebraicGeometry_formallyUnramified_of_forall_etale_pullback_snd
end P2MW
export P2MW.S_AlgebraicGeometry_formallyUnramified_of_forall_etale_pullback_snd (solution)

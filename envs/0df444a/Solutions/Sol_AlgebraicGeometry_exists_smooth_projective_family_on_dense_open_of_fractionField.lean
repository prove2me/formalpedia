-- Prove2me | solution 1 for AlgebraicGeometry.exists_smooth_projective_family_on_dense_open_of_fractionField
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-25T14:43:32.750671+00:00
-- url     : https://prove2.me/submissions/89214d82-8336-4471-97cb-fb4b44e51944

import Mathlib
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_isPullback_comp_eq_map
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_smoothLocus_le_preimage_of_isPullback

universe u


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace PhilipponFractionFieldCoefficients

/-- A finitely generated prime subalgebra of a fraction field is defined on
one principal open of any given affine model. The factorization uses the
actual field, not an abstractly isomorphic field. -/
lemma factor_fg_prime_subalgebra
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    (A : Subalgebra ℤ E) (hA : A.FG) :
    ∃ (s : B), s ≠ 0 ∧
      ∃ (γ : Localization.Away s →ₐ[B] E), Function.Injective γ ∧
        ∃ (φ : A →+* Localization.Away s),
          γ.toRingHom.comp φ = A.val.toRingHom := by
  classical
  obtain ⟨T, hT⟩ := hA
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors B) T
  have hs0 : (s : B) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s.property
  let γ : Localization.Away (s : B) →ₐ[B] E :=
    IsLocalization.Away.liftAlgHom (s : B)
      (f := Algebra.ofId B E)
      (isUnit_iff_ne_zero.mpr (by
        change algebraMap B E (s : B) ≠ 0
        simpa only [map_zero] using (IsFractionRing.injective B E).ne hs0))
  have hγbase (b : B) : γ (algebraMap B (Localization.Away (s : B)) b) =
      algebraMap B E b := γ.commutes b
  have hM : Submonoid.powers (s : B) ≤ nonZeroDivisors B := by
    intro b hb
    obtain ⟨n, rfl⟩ := by simpa only [Algebra.smul_def] using hb
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hs0)
  have hγ : Function.Injective γ := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq
      (Submonoid.powers (s : B)) γ.toRingHom).mpr
    intro x y
    change algebraMap B (Localization.Away (s : B)) x = _ ↔
      γ (algebraMap B (Localization.Away (s : B)) x) =
        γ (algebraMap B (Localization.Away (s : B)) y)
    rw [hγbase, hγbase]
    exact (IsLocalization.injective _ hM).eq_iff.trans
      (IsFractionRing.injective B E).eq_iff.symm
  let γz : Localization.Away (s : B) →ₐ[ℤ] E := { __ := γ.toRingHom, commutes' := by intro r; simp }
  have hTA : A ≤ γz.range := by
    rw [← hT]
    apply Algebra.adjoin_le
    intro x hx
    obtain ⟨b, hb⟩ := hs x hx
    have hb' : algebraMap B E b = algebraMap B E s * x := by simpa only [Algebra.smul_def] using hb
    refine ⟨algebraMap B (Localization.Away (s : B)) b *
      IsLocalization.Away.invSelf (s : B), ?_⟩
    change γ (_ * _) = x
    apply mul_left_cancel₀ (show algebraMap B E s ≠ 0 by
      simpa only [map_zero] using (IsFractionRing.injective B E).ne hs0)
    rw [map_mul, hγbase, hb']
    calc
      algebraMap B E s * (algebraMap B E s * x * γ (IsLocalization.Away.invSelf (s : B))) =
          (algebraMap B E s * x) * γ (algebraMap B (Localization.Away (s : B)) s *
            IsLocalization.Away.invSelf (s : B)) := by rw [map_mul, hγbase]; ring
      _ = algebraMap B E s * x := by
        rw [IsLocalization.Away.mul_invSelf, map_one]
        simp
  let e := AlgEquiv.ofInjective γz hγ
  let φ : A →+* Localization.Away (s : B) :=
    (e.symm.toAlgHom.comp (Subalgebra.inclusion hTA)).toRingHom
  refine ⟨s, hs0, γ, hγ, φ, ?_⟩
  ext x
  change γz (e.symm (Subalgebra.inclusion hTA x)) = (x : E)
  have he := congrArg (fun z : γz.range => (z : E))
    (e.apply_symm_apply (Subalgebra.inclusion hTA x))
  exact (AlgEquiv.ofInjective_apply γz hγ _).symm.trans he

end PhilipponFractionFieldCoefficients

namespace PhilipponFractionFieldCoefficients

lemma fractionRing_of_injective_tower
    {B A E : Type u} [CommRing B] [CommRing A] [Field E]
    [Algebra B A] [Algebra B E] [Algebra A E] [IsScalarTower B A E]
    [IsFractionRing B E] (h : Function.Injective (algebraMap A E)) :
    IsFractionRing A E := by
  haveI : FaithfulSMul A E := (faithfulSMul_iff_algebraMap_injective A E).mpr h
  apply IsFractionRing.of_field
  intro x
  obtain ⟨a, b, _hb, hx⟩ := IsFractionRing.div_surjective B x
  refine ⟨algebraMap B A a, algebraMap B A b, ?_⟩
  simpa only [← IsScalarTower.algebraMap_apply B A E] using hx.symm

end PhilipponFractionFieldCoefficients


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponProjectiveFamily

/-- A smooth projective scheme over the actual fraction field spreads to a
flat finitely presented projective scheme over a principal localization. -/
lemma exists_flat_projective_model
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    (C : Scheme.{u}) (n : ℕ)
    (ι : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E))
    [IsClosedImmersion ι] [Smooth (ι ≫ ProjSpace.π E n)] :
    ∃ (s : B), s ≠ 0 ∧
      ∃ (γ : Localization.Away s →ₐ[B] E), Function.Injective γ ∧
        ∃ (Y : Scheme.{u})
          (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
            (Localization.Away s))) (g : C ⟶ Y),
          IsClosedImmersion j ∧ Flat (j ≫ ProjSpace.π (Localization.Away s) n) ∧
          LocallyOfFinitePresentation (j ≫ ProjSpace.π (Localization.Away s) n) ∧
          IsPullback g (ι ≫ ProjSpace.π E n)
            (j ≫ ProjSpace.π (Localization.Away s) n)
            (Spec.map (CommRingCat.ofHom γ.toRingHom)) := by
  obtain ⟨A₀, hA₀, C₀, ι₀, g₀, hι₀, hflat₀, hfp₀, hpb₀, _⟩ :=
    ProjSpace.exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
      n C ι inferInstance inferInstance inferInstance
  obtain ⟨s, hs, γ, hγ, φ, hφ⟩ :=
    PhilipponFractionFieldCoefficients.factor_fg_prime_subalgebra B E A₀ hA₀
  let A := Localization.Away s
  letI : Algebra A₀ A := φ.toAlgebra
  letI : Algebra A E := γ.toRingHom.toAlgebra
  letI : IsScalarTower A₀ A E := IsScalarTower.of_algebraMap_eq fun x =>
    DFunLike.congr_fun hφ x |>.symm
  letI : IsClosedImmersion ι₀ := hι₀
  letI : Flat (ι₀ ≫ ProjSpace.π A₀ n) := hflat₀
  letI : LocallyOfFinitePresentation (ι₀ ≫ ProjSpace.π A₀ n) := hfp₀
  obtain ⟨Y, j, hj, e, hpbe, _⟩ :=
    ProjSpace.exists_isClosedImmersion_isPullback_comp_eq_map ι₀ A
  have hbase : Spec.map (CommRingCat.ofHom γ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap A₀ E)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change Spec.map (CommRingCat.ofHom (γ.toRingHom.comp φ)) = _
    rw [hφ]
    rfl
  have hw : g₀ ≫ (ι₀ ≫ ProjSpace.π A₀ n) =
      ((ι ≫ ProjSpace.π E n) ≫ Spec.map (CommRingCat.ofHom γ.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) := by
    rw [Category.assoc, hbase]
    exact hpb₀.w
  let g := hpbe.lift g₀
    ((ι ≫ ProjSpace.π E n) ≫ Spec.map (CommRingCat.ofHom γ.toRingHom)) hw
  have hpg : IsPullback g (ι ≫ ProjSpace.π E n)
      (j ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom γ.toRingHom)) := by
    refine IsPullback.of_right ?_ (hpbe.lift_snd _ _ _) hpbe
    rw [hpbe.lift_fst, hbase]
    exact hpb₀
  have hflat : Flat (j ≫ ProjSpace.π A n) :=
    MorphismProperty.of_isPullback hpbe hflat₀
  have hfp : LocallyOfFinitePresentation (j ≫ ProjSpace.π A n) :=
    MorphismProperty.of_isPullback hpbe hfp₀
  exact ⟨s, hs, γ, hγ, Y, j, g, hj, hflat, hfp, hpg⟩

end PhilipponProjectiveFamily


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponSmoothFamilyOpen

lemma smooth_of_comp_openImmersion
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (j : Y ⟶ Z)
    [IsOpenImmersion j] [LocallyOfFinitePresentation f] [Smooth (f ≫ j)] :
    Smooth f := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_unique
  intro x _
  have hx : x ∈ (f ≫ j).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  rw [Scheme.Hom.mem_smoothLocus] at hx ⊢
  apply (RingHom.FormallySmooth.respectsIso.cancel_left_isIso
    (j.stalkMap (f x)) (f.stalkMap x)).mp
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
  exact hx

/-- Smoothness of a flatly covered fibre of a proper finitely presented
morphism extends over a neighbourhood of that fibre's base point. -/
lemma exists_open_of_smooth_pullback
    {Y S C T : Scheme.{u}} (f : Y ⟶ S) (p : C ⟶ T)
    (b : T ⟶ S) (g : C ⟶ Y) (hpb : IsPullback g p f b)
    [IsProper f] [LocallyOfFinitePresentation f] [Smooth p] [Flat b]
    (η : S) (hη : η ∈ Set.range b) :
    ∃ U : S.Opens, η ∈ U ∧ Smooth (f ∣_ U) := by
  let bad : Set Y := (f.smoothLocus : Set Y)ᶜ
  have hbad : IsClosed bad := f.smoothLocus.isOpen.isClosed_compl
  let U : S.Opens := ⟨(f '' bad)ᶜ, (f.isClosedMap bad hbad).isOpen_compl⟩
  have hηU : η ∈ U := by
    rintro ⟨y, hy, hyη⟩
    obtain ⟨t, ht⟩ := hη
    obtain ⟨z, hzy, _⟩ := Scheme.Pullback.exists_preimage_pullback y t (hyη.trans ht.symm)
    let c := hpb.isoPullback.inv z
    have hc : g c = y := by
      change (hpb.isoPullback.inv ≫ g) z = y
      rw [hpb.isoPullback_inv_fst]
      exact hzy
    have hs := Scheme.Hom.smoothLocus_le_preimage_of_isPullback hpb
    have hcS : c ∈ p.smoothLocus := by rw [p.smoothLocus_eq_top]; trivial
    have hyS : y ∈ f.smoothLocus := by simpa only [Scheme.Hom.mem_preimage, hc] using hs hcS
    exact hy hyS
  have hle : f ⁻¹ᵁ U ≤ f.smoothLocus := by
    intro y hy
    by_contra h
    exact hy ⟨y, h, rfl⟩
  have hc : Smooth ((f ⁻¹ᵁ U).ι ≫ f) := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    apply top_unique
    intro x _
    exact hle x.property
  have hcomp : (f ∣_ U) ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f :=
    (isPullback_morphismRestrict f U).w
  haveI : Smooth ((f ∣_ U) ≫ U.ι) := by rw [hcomp]; exact hc
  exact ⟨U, hηU, smooth_of_comp_openImmersion (f ∣_ U) U.ι⟩

end PhilipponSmoothFamilyOpen


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponProjectiveFamily

/-- The given smooth projective scheme over the actual fraction field is
the exact generic fibre of a smooth proper family over a dense open of a
principal localization of the prescribed affine base. The projective
ambient model is retained. -/
theorem exists_smooth_projective_family_on_dense_open
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    (C : Scheme.{u}) (n : ℕ)
    (ι : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E))
    [IsClosedImmersion ι] [Smooth (ι ≫ ProjSpace.π E n)] :
    ∃ (s : B), s ≠ 0 ∧
      ∃ (γ : Localization.Away s →ₐ[B] E), Function.Injective γ ∧
        ∃ (Y : Scheme.{u})
          (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
            (Localization.Away s))), IsClosedImmersion j ∧
          ∃ U : (Spec (.of (Localization.Away s))).Opens,
            Dense (U : Set (Spec (.of (Localization.Away s)))) ∧
            ∃ (bU : Spec (.of E) ⟶ U)
              (gU : C ⟶ ((j ≫ ProjSpace.π (Localization.Away s) n) ⁻¹ᵁ U)),
              bU ≫ U.ι = Spec.map (CommRingCat.ofHom γ.toRingHom) ∧
              IsPullback gU (ι ≫ ProjSpace.π E n)
                ((j ≫ ProjSpace.π (Localization.Away s) n) ∣_ U) bU ∧
              Smooth ((j ≫ ProjSpace.π (Localization.Away s) n) ∣_ U) ∧
              IsProper ((j ≫ ProjSpace.π (Localization.Away s) n) ∣_ U) := by
  obtain ⟨s, hs, γ, hγ, Y, j, g, hj, hfl, hfp, hpb⟩ :=
    exists_flat_projective_model B E C n ι
  let A := Localization.Away s
  letI : Algebra A E := γ.toRingHom.toAlgebra
  letI : IsScalarTower B A E := IsScalarTower.of_algebraMap_eq fun b => (γ.commutes b).symm
  letI : IsFractionRing A E :=
    PhilipponFractionFieldCoefficients.fractionRing_of_injective_tower (B := B) (A := A) hγ
  letI : IsDomain A := Function.Injective.isDomain γ.toRingHom hγ
  letI : IsClosedImmersion j := hj
  let f := j ≫ ProjSpace.π A n
  letI : IsProper f := inferInstance
  letI : LocallyOfFinitePresentation f := hfp
  let b := Spec.map (CommRingCat.ofHom γ.toRingHom)
  letI : Module.Flat A E := IsLocalization.flat E (nonZeroDivisors A)
  letI : Flat b := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let e : Spec (.of E) := default
  obtain ⟨U, hU, hsm⟩ :=
    PhilipponSmoothFamilyOpen.exists_open_of_smooth_pullback f (ι ≫ ProjSpace.π E n)
      b g hpb (b e) ⟨e, rfl⟩
  have hbU : Set.range b ⊆ U := by
    rintro x ⟨e', rfl⟩
    change b e' ∈ U
    rw [Subsingleton.elim e' e]
    exact hU
  have hdU : Dense (U : Set (Spec (.of A))) :=
    U.isOpen.dense ⟨b e, hU⟩
  let bU := IsOpenImmersion.lift U.ι b (by simpa only [Scheme.Opens.range_ι] using hbU)
  have hb : bU ≫ U.ι = b := IsOpenImmersion.lift_fac _ _ _
  let hpu := (isPullback_morphismRestrict f U).flip
  have hw : g ≫ f = ((ι ≫ ProjSpace.π E n) ≫ bU) ≫ U.ι := by
    rw [Category.assoc, hb]
    exact hpb.w
  let gU := hpu.lift g ((ι ≫ ProjSpace.π E n) ≫ bU) hw
  have hpU : IsPullback gU (ι ≫ ProjSpace.π E n) (f ∣_ U) bU := by
    refine IsPullback.of_right ?_ (hpu.lift_snd _ _ _) hpu
    rw [hpu.lift_fst, hb]
    exact hpb
  have hpr : IsProper (f ∣_ U) := MorphismProperty.of_isPullback hpu inferInstance
  exact ⟨s, hs, γ, hγ, Y, j, hj, U, hdU, bU, gU, hb, hpU, hsm, hpr⟩

end PhilipponProjectiveFamily

theorem solution
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    (C : Scheme.{u}) (n : ℕ)
    (ι : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E))
    [IsClosedImmersion ι] [Smooth (ι ≫ ProjSpace.π E n)] :
    ∃ (s : B), s ≠ 0 ∧
      ∃ (γ : Localization.Away s →ₐ[B] E), Function.Injective γ ∧
        ∃ (Y : Scheme.{u})
          (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
            (Localization.Away s))), IsClosedImmersion j ∧
          ∃ U : (Spec (.of (Localization.Away s))).Opens,
            Dense (U : Set (Spec (.of (Localization.Away s)))) ∧
            ∃ (bU : Spec (.of E) ⟶ U)
              (gU : C ⟶ ((j ≫ ProjSpace.π (Localization.Away s) n) ⁻¹ᵁ U)),
              bU ≫ U.ι = Spec.map (CommRingCat.ofHom γ.toRingHom) ∧
              IsPullback gU (ι ≫ ProjSpace.π E n)
                ((j ≫ ProjSpace.π (Localization.Away s) n) ∣_ U) bU ∧
              Smooth ((j ≫ ProjSpace.π (Localization.Away s) n) ∣_ U) ∧
              IsProper ((j ≫ ProjSpace.π (Localization.Away s) n) ∣_ U) := by
  exact PhilipponProjectiveFamily.exists_smooth_projective_family_on_dense_open B E C n ι

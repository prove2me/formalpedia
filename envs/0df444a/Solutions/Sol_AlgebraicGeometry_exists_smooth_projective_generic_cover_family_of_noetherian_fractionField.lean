-- Prove2me | solution 1 for AlgebraicGeometry.exists_smooth_projective_generic_cover_family_of_noetherian_fractionField
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-25T18:49:02.711989+00:00
-- url     : https://prove2.me/submissions/3a34f030-948b-47bb-922f-e2dd9030d5f7

import Mathlib
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_isPullback_comp_eq_map
import Theorems.Thm_AlgebraicGeometry_exists_smooth_proper_cover_on_dense_open_of_noetherian_fractionField

universe u
noncomputable section
set_option linter.style.haveILetI false


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PhilipponGenericMorphismSpread

/-- Canonical comparison of two pullbacks with compatible base maps. -/
def changeBase {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    pullback f a ⟶ pullback f b :=
  pullback.lift (pullback.fst f a) (pullback.snd f a ≫ c)
    (by rw [Category.assoc, hc]; exact pullback.condition)

@[reassoc (attr := simp)] lemma changeBase_fst {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    changeBase f a b c hc ≫ pullback.fst f b = pullback.fst f a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] lemma changeBase_snd {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    changeBase f a b c hc ≫ pullback.snd f b = pullback.snd f a ≫ c :=
  pullback.lift_snd _ _ _


end PhilipponGenericMorphismSpread

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponGenericMorphismSpread
namespace PhilipponProperCoverSpread

lemma changeBase_isPullback {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    IsPullback (changeBase f a b c hc) (pullback.snd f a) (pullback.snd f b) c := by
  refine IsPullback.of_right ?_ (changeBase_snd _ _ _ _ _) (IsPullback.of_hasPullback f b)
  rw [changeBase_fst, hc]
  exact IsPullback.of_hasPullback f a


end PhilipponProperCoverSpread


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
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PhilipponGenericCoverComparison

/-- Cartesian generic models transport a smooth surjective cover to the
actual pullback families, keeping an exact recovery equation. -/
lemma transport_smooth_surjective_cover
    {C₁ C₂ Y₁ Y₂ T U : Scheme.{u}}
    (p₁ : C₁ ⟶ T) (p₂ : C₂ ⟶ T) (f₁ : Y₁ ⟶ U) (f₂ : Y₂ ⟶ U)
    (b : T ⟶ U) (q₁ : C₁ ⟶ Y₁) (q₂ : C₂ ⟶ Y₂)
    (hp₁ : IsPullback q₁ p₁ f₁ b) (hp₂ : IsPullback q₂ p₂ f₂ b)
    (g : C₁ ⟶ C₂) (hg : g ≫ p₂ = p₁) (hgs : Function.Surjective g) [Smooth p₁] :
    ∃ g' : pullback f₁ b ⟶ pullback f₂ b,
      g' ≫ pullback.snd f₂ b = pullback.snd f₁ b ∧
      Function.Surjective g' ∧ Smooth (pullback.snd f₁ b) ∧
      hp₁.isoPullback.hom ≫ g' = g ≫ hp₂.isoPullback.hom := by
  let e₁ := hp₁.isoPullback
  let e₂ := hp₂.isoPullback
  let g' := e₁.inv ≫ g ≫ e₂.hom
  haveI : Surjective g := ⟨hgs⟩
  have hsur' : Surjective (e₁.inv ≫ g ≫ e₂.hom) := inferInstance
  have hsur : Function.Surjective g' := hsur'.1
  have hscomp : Smooth (e₁.hom ≫ pullback.snd f₁ b) := by
    rw [hp₁.isoPullback_hom_snd]
    infer_instance
  have hsm : Smooth (pullback.snd f₁ b) :=
    (MorphismProperty.cancel_left_of_respectsIso @Smooth e₁.hom _).mp hscomp
  have hover : g' ≫ pullback.snd f₂ b = pullback.snd f₁ b := by
    dsimp only [g', e₂]
    rw [Category.assoc, Category.assoc, hp₂.isoPullback_hom_snd, hg]
    exact hp₁.isoPullback_inv_snd
  refine ⟨g', hover, hsur, hsm, ?_⟩
  dsimp only [g', e₁, e₂]
  simp

end PhilipponGenericCoverComparison


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
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponGenericMorphismSpread
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponProjectiveGenericCoverSpread

/-- A given smooth projective generic cover acquires a projective model and
spreads to a smooth proper covering family, retaining its original maps. -/
theorem exists_projective_cover_family
    (B E : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) [IsProper f] [LocallyOfFinitePresentation f]
    (C : Scheme.{u}) (n : ℕ)
    (ι : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E))
    [IsClosedImmersion ι] [Smooth (ι ≫ ProjSpace.π E n)]
    (g : C ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap B E))))
    (hg : g ≫ pullback.snd f _ = ι ≫ ProjSpace.π E n) (hgs : Function.Surjective g) :
    ∃ a : B, a ≠ 0 ∧
      ∃ γ : Localization.Away a →ₐ[B] E, Function.Injective γ ∧
        ∃ (M : Scheme.{u})
          (iM : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (Localization.Away a)))
          (gM : C ⟶ M), IsClosedImmersion iM ∧
          IsPullback gM (ι ≫ ProjSpace.π E n) (iM ≫ ProjSpace.π (Localization.Away a) n)
            (Spec.map (CommRingCat.ofHom γ.toRingHom)) ∧
          ∃ (S : Scheme.{u}) (j : S ⟶ Spec (.of (Localization.Away a))),
            IsOpenImmersion j ∧ DenseRange j ∧
            ∃ (Y Z : Scheme.{u}) (pY : Y ⟶ S) (pZ : Z ⟶ S) (tY : Y ⟶ M) (tZ : Z ⟶ X),
              IsPullback tY pY (iM ≫ ProjSpace.π (Localization.Away a) n) j ∧
              IsPullback tZ pZ f (j ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away a)))) ∧
              Smooth pY ∧ IsProper pY ∧ Flat pZ ∧ IsProper pZ ∧
              ∃ h : Y ⟶ Z, h ≫ pZ = pY ∧ IsProper h ∧ Function.Surjective h ∧
                ∃ (b : Spec (.of E) ⟶ S) (eC : C ⟶ Y)
                  (eX : pullback f (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶ Z),
                  b ≫ j = Spec.map (CommRingCat.ofHom γ.toRingHom) ∧
                  IsPullback eC (ι ≫ ProjSpace.π E n) pY b ∧
                  IsPullback eX (pullback.snd f _) pZ b ∧
                  eC ≫ tY = gM ∧ eX ≫ tZ = pullback.fst f _ ∧ eC ≫ h = g ≫ eX := by
  obtain ⟨a, ha, γ, hγ, M, iM, gM, hiM, _hflatM, hfpM, hpM⟩ :=
    PhilipponProjectiveFamily.exists_flat_projective_model B E C n ι
  let A := Localization.Away a
  letI : Algebra A E := γ.toRingHom.toAlgebra
  letI : IsScalarTower B A E := IsScalarTower.of_algebraMap_eq fun x => (γ.commutes x).symm
  letI : IsFractionRing A E :=
    PhilipponFractionFieldCoefficients.fractionRing_of_injective_tower (B := B) (A := A) hγ
  haveI : IsDomain A := Function.Injective.isDomain γ.toRingHom hγ
  let bE := Spec.map (CommRingCat.ofHom (algebraMap B E))
  let bA := Spec.map (CommRingCat.ofHom (algebraMap B A))
  let dE := Spec.map (CommRingCat.ofHom γ.toRingHom)
  have hdE : dE ≫ bA = bE := by
    dsimp only [dE, bA, bE]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) γ.comp_algebraMap
  let fM := iM ≫ ProjSpace.π A n
  haveI : IsClosedImmersion iM := hiM
  haveI : IsProper fM := inferInstance
  haveI : LocallyOfFinitePresentation fM := hfpM
  let fA := pullback.snd f bA
  let q := changeBase f bE bA dE hdE
  have hpX := PhilipponProperCoverSpread.changeBase_isPullback f bE bA dE hdE
  obtain ⟨gA, hgA, hgsA, hsmA, hrecA⟩ :=
    PhilipponGenericCoverComparison.transport_smooth_surjective_cover
      (ι ≫ ProjSpace.π E n) (pullback.snd f bE) fM fA dE gM q hpM hpX g hg hgs
  haveI : Smooth (pullback.snd fM dE) := hsmA
  obtain ⟨S, j, hj, hdj, Y, Z, pY, pZ, tY, tA, hpY, hpZ, hflZ,
    h, hover, hsmY, hprY, hproper, hsurj, b, cY, cZ, hb, heY, heZ, hcY, hcZ, hrec⟩ :=
    AlgebraicGeometry.exists_smooth_proper_cover_on_dense_open_of_noetherian_fractionField A E fM fA gA hgA hgsA
  let tZ := tA ≫ pullback.fst f bA
  have hptZ : IsPullback tZ pZ f (j ≫ bA) :=
    hpZ.paste_horiz (IsPullback.of_hasPullback f bA)
  have hprZ : IsProper pZ := MorphismProperty.of_isPullback hptZ inferInstance
  let eC := hpM.isoPullback.hom ≫ cY
  let eX := hpX.isoPullback.hom ≫ cZ
  have heCt : eC ≫ tY = gM := by
    dsimp only [eC]
    rw [Category.assoc, hcY, hpM.isoPullback_hom_fst]
  have heCp : eC ≫ pY = (ι ≫ ProjSpace.π E n) ≫ b := by
    dsimp only [eC]
    rw [Category.assoc, heY.w, ← Category.assoc, hpM.isoPullback_hom_snd]
  have heXp : eX ≫ pZ = pullback.snd f bE ≫ b := by
    dsimp only [eX]
    rw [Category.assoc, heZ.w, ← Category.assoc, hpX.isoPullback_hom_snd]
  have heXt : eX ≫ tA = q := by
    dsimp only [eX]
    rw [Category.assoc, hcZ, hpX.isoPullback_hom_fst]
  have heC : IsPullback eC (ι ≫ ProjSpace.π E n) pY b := by
    refine IsPullback.of_right ?_ heCp hpY
    rw [heCt, hb]
    exact hpM
  have heX : IsPullback eX (pullback.snd f bE) pZ b := by
    refine IsPullback.of_right ?_ heXp hpZ
    rw [heXt, hb]
    exact hpX
  have heXorig : eX ≫ tZ = pullback.fst f bE := by
    dsimp only [tZ]
    rw [← Category.assoc, heXt]
    exact changeBase_fst _ _ _ _ _
  have hrecover : eC ≫ h = g ≫ eX := by
    dsimp only [eC, eX]
    rw [Category.assoc, hrec, ← Category.assoc, hrecA, Category.assoc]
  exact ⟨a, ha, γ, hγ, M, iM, gM, hiM, hpM, S, j, hj, hdj, Y, Z, pY, pZ, tY, tZ,
    hpY, hptZ, hsmY, hprY, hflZ, hprZ, h, hover, hproper, hsurj,
    b, eC, eX, hb, heC, heX, heCt, heXorig, hrecover⟩

end PhilipponProjectiveGenericCoverSpread

theorem solution
    (B E : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) [IsProper f] [LocallyOfFinitePresentation f]
    (C : Scheme.{u}) (n : ℕ)
    (ι : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E))
    [IsClosedImmersion ι] [Smooth (ι ≫ ProjSpace.π E n)]
    (g : C ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap B E))))
    (hg : g ≫ pullback.snd f _ = ι ≫ ProjSpace.π E n) (hgs : Function.Surjective g) :
    ∃ a : B, a ≠ 0 ∧
      ∃ γ : Localization.Away a →ₐ[B] E, Function.Injective γ ∧
        ∃ (M : Scheme.{u})
          (iM : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (Localization.Away a)))
          (gM : C ⟶ M), IsClosedImmersion iM ∧
          IsPullback gM (ι ≫ ProjSpace.π E n) (iM ≫ ProjSpace.π (Localization.Away a) n)
            (Spec.map (CommRingCat.ofHom γ.toRingHom)) ∧
          ∃ (S : Scheme.{u}) (j : S ⟶ Spec (.of (Localization.Away a))),
            IsOpenImmersion j ∧ DenseRange j ∧
            ∃ (Y Z : Scheme.{u}) (pY : Y ⟶ S) (pZ : Z ⟶ S) (tY : Y ⟶ M) (tZ : Z ⟶ X),
              IsPullback tY pY (iM ≫ ProjSpace.π (Localization.Away a) n) j ∧
              IsPullback tZ pZ f (j ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away a)))) ∧
              Smooth pY ∧ IsProper pY ∧ Flat pZ ∧ IsProper pZ ∧
              ∃ h : Y ⟶ Z, h ≫ pZ = pY ∧ IsProper h ∧ Function.Surjective h ∧
                ∃ (b : Spec (.of E) ⟶ S) (eC : C ⟶ Y)
                  (eX : pullback f (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶ Z),
                  b ≫ j = Spec.map (CommRingCat.ofHom γ.toRingHom) ∧
                  IsPullback eC (ι ≫ ProjSpace.π E n) pY b ∧
                  IsPullback eX (pullback.snd f _) pZ b ∧
                  eC ≫ tY = gM ∧ eX ≫ tZ = pullback.fst f _ ∧ eC ≫ h = g ≫ eX := by
  exact PhilipponProjectiveGenericCoverSpread.exists_projective_cover_family B E f C n ι g hg hgs

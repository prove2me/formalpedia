-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.smoothLocus_le_preimage_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/38c83833-5e98-51fa-8d1c-9fc85a97cf6b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_smoothLocus_le_preimage_of_isPullback

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_smoothLocus_le_preimage_of_isPullback.AlgebraicGeometry TensorProduct"

universe u

namespace Module
p2m_export "Module" "reflection FaithfullyFlat.lTensor_reflects_triviality Flat support equiv free_of_flat_of_isLocalRing Flat.of_flat_tensorProduct Free mk FaithfullyFlat Free.of_equiv support_subset_of_injective Flat.of_linearEquiv freeLocus FaithfullyFlat.of_flat_of_isLocalHom restrictScalars FinitePresentation mem_freeLocus_iff_tensor freeLocus_congr notMem_support_iff"
p2m_open "Module"

variable {S S' : Type*} [CommRing S] [CommRing S'] [Algebra S S']

noncomputable def locTensorBaseChangeEquiv (M : Type*) [AddCommGroup M] [Module S M]
    (q' : PrimeSpectrum S')
    [Algebra (Localization.AtPrime (q'.comap (algebraMap S S')).asIdeal) (Localization.AtPrime q'.asIdeal)]
    [IsScalarTower S (Localization.AtPrime (q'.comap (algebraMap S S')).asIdeal) (Localization.AtPrime q'.asIdeal)] :
    (Localization.AtPrime q'.asIdeal) ⊗[S'] (S' ⊗[S] M) ≃ₗ[Localization.AtPrime q'.asIdeal]
      (Localization.AtPrime q'.asIdeal) ⊗[Localization.AtPrime (q'.comap (algebraMap S S')).asIdeal]
        ((Localization.AtPrime (q'.comap (algebraMap S S')).asIdeal) ⊗[S] M) :=
  (AlgebraTensorModule.cancelBaseChange S S' (Localization.AtPrime q'.asIdeal) (Localization.AtPrime q'.asIdeal) M).trans
    (AlgebraTensorModule.cancelBaseChange S (Localization.AtPrime (q'.comap (algebraMap S S')).asIdeal)
      (Localization.AtPrime q'.asIdeal) (Localization.AtPrime q'.asIdeal) M).symm

theorem comap_notMem_support_of_notMem_support_baseChange [Module.Flat S S']
    (M : Type*) [AddCommGroup M] [Module S M]
    (q' : PrimeSpectrum S') (hq' : q' ∉ Module.support S' (S' ⊗[S] M)) :
    q'.comap (algebraMap S S') ∉ Module.support S M := by
  set q := q'.comap (algebraMap S S') with hq
  haveI : q'.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver q.asIdeal q'.asIdeal
  haveI : IsLocalHom (algebraMap (Localization.AtPrime q.asIdeal) (Localization.AtPrime q'.asIdeal)) :=
    Localization.isLocalHom_localRingHom q.asIdeal q'.asIdeal (algebraMap S S') Ideal.LiesOver.over
  haveI : Module.FaithfullyFlat (Localization.AtPrime q.asIdeal) (Localization.AtPrime q'.asIdeal) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [Module.notMem_support_iff] at hq' ⊢

  have e₁ := (LocalizedModule.equivTensorProduct q'.asIdeal.primeCompl (S' ⊗[S] M)).toEquiv
  haveI : Subsingleton ((Localization.AtPrime q'.asIdeal) ⊗[S'] (S' ⊗[S] M)) := e₁.symm.subsingleton
  haveI : Subsingleton ((Localization.AtPrime q'.asIdeal) ⊗[Localization.AtPrime q.asIdeal]
      ((Localization.AtPrime q.asIdeal) ⊗[S] M)) :=
    (locTensorBaseChangeEquiv M q').symm.toEquiv.subsingleton
  haveI : Subsingleton ((Localization.AtPrime q.asIdeal) ⊗[S] M) :=
    Module.FaithfullyFlat.lTensor_reflects_triviality (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q'.asIdeal) _
  exact (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl M).toEquiv.subsingleton

theorem comap_mem_freeLocus_of_mem_freeLocus_baseChange [Module.Flat S S']
    (N : Type*) [AddCommGroup N] [Module S N] [Module.FinitePresentation S N]
    (q' : PrimeSpectrum S') (hq' : q' ∈ Module.freeLocus S' (S' ⊗[S] N)) :
    q'.comap (algebraMap S S') ∈ Module.freeLocus S N := by
  set q := q'.comap (algebraMap S S') with hq
  haveI : q'.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver q.asIdeal q'.asIdeal
  haveI : IsLocalHom (algebraMap (Localization.AtPrime q.asIdeal) (Localization.AtPrime q'.asIdeal)) :=
    Localization.isLocalHom_localRingHom q.asIdeal q'.asIdeal (algebraMap S S') Ideal.LiesOver.over
  haveI : Module.FaithfullyFlat (Localization.AtPrime q.asIdeal) (Localization.AtPrime q'.asIdeal) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [Module.mem_freeLocus_iff_tensor _ (Localization.AtPrime q'.asIdeal)] at hq'
  rw [Module.mem_freeLocus_iff_tensor _ (Localization.AtPrime q.asIdeal)]
  haveI := hq'
  haveI : Module.Free (Localization.AtPrime q'.asIdeal)
      ((Localization.AtPrime q'.asIdeal) ⊗[Localization.AtPrime q.asIdeal]
        ((Localization.AtPrime q.asIdeal) ⊗[S] N)) :=
    Module.Free.of_equiv (locTensorBaseChangeEquiv N q')
  haveI : Module.Flat (Localization.AtPrime q.asIdeal) ((Localization.AtPrime q.asIdeal) ⊗[S] N) :=
    Module.Flat.of_flat_tensorProduct (Localization.AtPrime q.asIdeal) _ (Localization.AtPrime q'.asIdeal)
  exact Module.free_of_flat_of_isLocalRing

end Module

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι Scheme.Hom.preimage_smoothLocus_eq Surjective Scheme.Hom.isPullback_resLE formallySmooth_stalkMap_iff isPushout_appTop_of_isPullback Scheme.Hom IsAffine Spec Scheme.Hom.stalkMap_comp Spec.map Scheme Smooth IsOpenImmersion Scheme.Hom.comp_base Flat isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE Scheme.Hom.mem_smoothLocus Scheme.Opens.ι IsAffineOpen Scheme.Opens Scheme.Hom.app_eq_appLE LocallyOfFinitePresentation Scheme.Hom.comp_preimage Scheme.arrowStalkMapSpecIso geometrically Scheme.Hom.smoothLocus_le_preimage_of_isPullback"
namespace SmoothLocusBC
p2m_open "AlgebraicGeometry"

open Algebra.TensorProduct in

theorem flat_right_baseChange {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
    [Module.Flat A A'] :
    letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    Module.Flat B (A' ⊗[A] B) := by
  letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra

  let e₀ := (Algebra.TensorProduct.comm A A' B).toLinearEquiv.toAddEquiv
  have hsmul : ∀ (b : B) (z : A' ⊗[A] B), e₀ (b • z) = b • e₀ z := by
    intro b z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
    | tmul t b₀ =>
      change (Algebra.TensorProduct.comm A A' B) (((1 : A') ⊗ₜ[A] b) * (t ⊗ₜ[A] b₀)) =
        b • (Algebra.TensorProduct.comm A A' B) (t ⊗ₜ[A] b₀)
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.comm_tmul,
        Algebra.TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  let e : (A' ⊗[A] B) ≃ₗ[B] (B ⊗[A] A') := { e₀ with map_smul' := hsmul }
  exact Module.Flat.of_linearEquiv e

set_option maxHeartbeats 3200000 in

theorem isSmoothAt_comap_of_isSmoothAt_baseChange
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
    [Algebra.FinitePresentation A B] [Module.Flat A A']
    (q' : Ideal (A' ⊗[A] B)) [q'.IsPrime] (h : Algebra.IsSmoothAt A' q') :
    Algebra.IsSmoothAt A (q'.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B).toRingHom) := by
  letI algB : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Flat B (A' ⊗[A] B) := flat_right_baseChange

  let P' : PrimeSpectrum (A' ⊗[A] B) := ⟨q', inferInstance⟩
  have hP' : P' ∈ Algebra.smoothLocus A' (A' ⊗[A] B) := h
  rw [Algebra.smoothLocus_eq_compl_support_inter] at hP'
  obtain ⟨hH', hΩ'⟩ := hP'
  have halg : (algebraMap B (A' ⊗[A] B)) = (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B).toRingHom := rfl
  suffices hP : P'.comap (algebraMap B (A' ⊗[A] B)) ∈ Algebra.smoothLocus A B by
    exact hP
  rw [Algebra.smoothLocus_eq_compl_support_inter]
  refine ⟨?_, ?_⟩
  ·
    let m : Algebra.H1Cotangent A B →ₗ[B] Algebra.H1Cotangent A' (A' ⊗[A] B) :=
      Algebra.H1Cotangent.map A A' B (A' ⊗[A] B)
    let eH : (A' ⊗[A] B) ⊗[B] Algebra.H1Cotangent A B →ₗ[A' ⊗[A] B] Algebra.H1Cotangent A' (A' ⊗[A] B) :=
      LinearMap.liftBaseChange (A' ⊗[A] B) m

    let c : A' ⊗[A] Algebra.H1Cotangent A B →ₗ[A] (A' ⊗[A] B) ⊗[B] Algebra.H1Cotangent A B :=
      TensorProduct.lift
        { toFun := fun t => (TensorProduct.mk B (A' ⊗[A] B) (Algebra.H1Cotangent A B) (t ⊗ₜ[A] (1 : B))).restrictScalars A
          map_add' := fun t t' => by ext x; simp [TensorProduct.add_tmul]
          map_smul' := fun a t => by
            ext x
            simp only [LinearMap.coe_restrictScalars, TensorProduct.mk_apply, RingHom.id_apply, LinearMap.smul_apply]
            rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul'] }
    have hc : ∀ (t : A') (x : Algebra.H1Cotangent A B), c (t ⊗ₜ[A] x) = (t ⊗ₜ[A] (1 : B)) ⊗ₜ[B] x := fun t x => rfl
    have hcomp : ∀ w, eH (c w) = Algebra.tensorH1CotangentOfFlat A B A' w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
      | tmul t x =>
        rw [hc, Algebra.tensorH1CotangentOfFlat_tmul]
        change (t ⊗ₜ[A] (1 : B)) • m x = t • m x
        rw [show (t ⊗ₜ[A] (1 : B)) = algebraMap A' (A' ⊗[A] B) t from rfl, algebraMap_smul]
    have hcsurj : Function.Surjective c := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | add x y hx hy =>
        obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, map_add _ _ _⟩
      | tmul s x =>
        induction s using TensorProduct.induction_on with
        | zero => exact ⟨0, by rw [map_zero, TensorProduct.zero_tmul]⟩
        | add s₁ s₂ h₁ h₂ =>
          obtain ⟨a, ha⟩ := h₁; obtain ⟨b, hb⟩ := h₂
          exact ⟨a + b, by rw [map_add, ha, hb, TensorProduct.add_tmul]⟩
        | tmul t b =>
          refine ⟨t ⊗ₜ[A] (b • x), ?_⟩
          rw [hc, ← TensorProduct.smul_tmul]
          congr 1
          rw [Algebra.smul_def]
          change ((1 : A') ⊗ₜ[A] b) * (t ⊗ₜ[A] (1 : B)) = t ⊗ₜ[A] b
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    have hbij : Function.Bijective eH := by
      constructor
      · intro z₁ z₂ hz
        obtain ⟨w₁, rfl⟩ := hcsurj z₁
        obtain ⟨w₂, rfl⟩ := hcsurj z₂
        rw [hcomp, hcomp] at hz
        rw [(Algebra.tensorH1CotangentOfFlat A B A').injective hz]
      · intro y
        obtain ⟨w, rfl⟩ := (Algebra.tensorH1CotangentOfFlat A B A').surjective y
        exact ⟨c w, hcomp w⟩
    let eH' := LinearEquiv.ofBijective eH hbij
    have hsupp : P' ∉ Module.support (A' ⊗[A] B) ((A' ⊗[A] B) ⊗[B] Algebra.H1Cotangent A B) := by
      intro hmem
      apply hH'
      exact Module.support_subset_of_injective eH'.toLinearMap eH'.injective hmem
    exact Module.comap_notMem_support_of_notMem_support_baseChange (Algebra.H1Cotangent A B) P' hsupp
  ·
    let eΩ : (A' ⊗[A] B) ⊗[B] Ω[B⁄A] ≃ₗ[A' ⊗[A] B] Ω[(A' ⊗[A] B)⁄A'] :=
      KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)
    have hfree : P' ∈ Module.freeLocus (A' ⊗[A] B) ((A' ⊗[A] B) ⊗[B] Ω[B⁄A]) := by
      rw [Module.freeLocus_congr eΩ]
      exact hΩ'
    exact Module.comap_mem_freeLocus_of_mem_freeLocus_baseChange (Ω[B⁄A]) P' hfree

end AlgebraicGeometry.SmoothLocusBC

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι Scheme.Hom.preimage_smoothLocus_eq Surjective Scheme.Hom.isPullback_resLE formallySmooth_stalkMap_iff isPushout_appTop_of_isPullback Scheme.Hom IsAffine Spec Scheme.Hom.stalkMap_comp Spec.map Scheme Smooth IsOpenImmersion Scheme.Hom.comp_base Flat isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE Scheme.Hom.mem_smoothLocus Scheme.Opens.ι IsAffineOpen Scheme.Opens Scheme.Hom.app_eq_appLE LocallyOfFinitePresentation Scheme.Hom.comp_preimage Scheme.arrowStalkMapSpecIso geometrically Scheme.Hom.smoothLocus_le_preimage_of_isPullback"
namespace SmoothLocusBC
p2m_open "AlgebraicGeometry"

theorem formallySmooth_localRingHom_iff {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (q : Ideal B) [q.IsPrime] :
    (Localization.localRingHom (q.comap φ) q φ rfl).FormallySmooth ↔
      letI := φ.toAlgebra; Algebra.FormallySmooth A (Localization.AtPrime q) := by
  letI := φ.toAlgebra
  letI alg1 : Algebra (Localization.AtPrime (q.comap φ)) (Localization.AtPrime q) :=
    (Localization.localRingHom (q.comap φ) q φ rfl).toAlgebra
  haveI : IsScalarTower A (Localization.AtPrime (q.comap φ)) (Localization.AtPrime q) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply A B (Localization.AtPrime q),
      Localization.localRingHom_to_map]
    rfl
  show Algebra.FormallySmooth (Localization.AtPrime (q.comap φ)) (Localization.AtPrime q) ↔
    Algebra.FormallySmooth A (Localization.AtPrime q)
  constructor
  · intro h
    haveI : Algebra.FormallySmooth A (Localization.AtPrime (q.comap φ)) :=
      Algebra.FormallySmooth.of_isLocalization (q.comap φ).primeCompl
    exact Algebra.FormallySmooth.comp A (Localization.AtPrime (q.comap φ)) (Localization.AtPrime q)
  · intro h
    exact Algebra.FormallySmooth.localization_base (q.comap φ).primeCompl

theorem mem_smoothLocus_SpecMap_iff {A B : CommRingCat.{u}} (φ : A ⟶ B)
    [LocallyOfFinitePresentation (Spec.map φ)] (q : PrimeSpectrum B) :
    (q : ↥(Spec B)) ∈ (Spec.map φ).smoothLocus ↔ letI := φ.hom.toAlgebra; Algebra.IsSmoothAt A q.asIdeal := by
  haveI : (RingHom.toMorphismProperty (fun f => RingHom.FormallySmooth f)).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.FormallySmooth.respectsIso
  refine Scheme.Hom.mem_smoothLocus.trans ?_
  refine ((RingHom.toMorphismProperty (fun f => RingHom.FormallySmooth f)).arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso φ q)).trans ?_
  exact formallySmooth_localRingHom_iff φ.hom q.asIdeal

end AlgebraicGeometry.SmoothLocusBC

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι Scheme.Hom.preimage_smoothLocus_eq Surjective Scheme.Hom.isPullback_resLE formallySmooth_stalkMap_iff isPushout_appTop_of_isPullback Scheme.Hom IsAffine Spec Scheme.Hom.stalkMap_comp Spec.map Scheme Smooth IsOpenImmersion Scheme.Hom.comp_base Flat isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE Scheme.Hom.mem_smoothLocus Scheme.Opens.ι IsAffineOpen Scheme.Opens Scheme.Hom.app_eq_appLE LocallyOfFinitePresentation Scheme.Hom.comp_preimage Scheme.arrowStalkMapSpecIso geometrically Scheme.Hom.smoothLocus_le_preimage_of_isPullback"
namespace SmoothLocusBC
p2m_open "AlgebraicGeometry"

open _root_.Algebra _root_.CategoryTheory.Algebra _root_.TensorProduct.Algebra in

theorem isSmoothAt_congr {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {p q : Ideal A}
    [p.IsPrime] [q.IsPrime] (h : p = q) : Algebra.IsSmoothAt R p ↔ Algebra.IsSmoothAt R q := by
  subst h; exact Iff.rfl

theorem isSmoothAt_comap_algEquiv {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (Q : Ideal B) [Q.IsPrime]
    (h : Algebra.IsSmoothAt R Q) : Algebra.IsSmoothAt R (Q.comap e.toRingHom) := by
  have H : (Q.comap e.toRingHom).primeCompl.map e.toRingEquiv.toMonoidHom = Q.primeCompl := by
    ext x
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, Ideal.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨e.symm x, by simpa using hx, by simp⟩
  let re : Localization.AtPrime (Q.comap e.toRingHom) ≃+* Localization.AtPrime Q :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (Q.comap e.toRingHom)) (Localization.AtPrime Q)
      e.toRingEquiv H
  let ae : Localization.AtPrime (Q.comap e.toRingHom) ≃ₐ[R] Localization.AtPrime Q :=
    AlgEquiv.ofRingEquiv (f := re) fun r => by
      rw [IsScalarTower.algebraMap_apply R A (Localization.AtPrime (Q.comap e.toRingHom)),
        IsScalarTower.algebraMap_apply R B (Localization.AtPrime Q)]
      simp only [re]
      rw [IsLocalization.ringEquivOfRingEquiv_eq]
      simp
  haveI : Algebra.FormallySmooth R (Localization.AtPrime Q) := h
  exact Algebra.FormallySmooth.of_equiv ae.symm

theorem isSmoothAt_comap_of_isSmoothAt_of_isPushout
    {A B A' C : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing C]
    [Algebra A B] [Algebra A A'] [Algebra A' C] [Algebra B C] [Algebra A C]
    [IsScalarTower A A' C] [IsScalarTower A B C] [Algebra.IsPushout A A' B C]
    [Algebra.FinitePresentation A B] [Module.Flat A A']
    (Q : Ideal C) [Q.IsPrime] (h : Algebra.IsSmoothAt A' Q) :
    Algebra.IsSmoothAt A (Q.comap (algebraMap B C)) := by
  let e : A' ⊗[A] B ≃ₐ[A'] C := Algebra.IsPushout.equiv A A' B C
  have h1 : Algebra.IsSmoothAt A' (Q.comap e.toRingHom) := isSmoothAt_comap_algEquiv e Q h
  have h2 := isSmoothAt_comap_of_isSmoothAt_baseChange (A := A) (B := B) (A' := A')
    (Q.comap e.toRingHom) h1
  have heq : (Q.comap e.toRingHom).comap
      (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B).toRingHom = Q.comap (algebraMap B C) := by
    rw [Ideal.comap_comap]
    congr 1
    ext b
    simp [e, Algebra.IsPushout.equiv_tmul]
  exact (isSmoothAt_congr heq).mp h2

theorem smoothLocus_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] : f.smoothLocus = g.smoothLocus := by
  subst e; rfl

theorem smoothLocus_comp_of_isOpenImmersion {X Y Z : Scheme.{u}} (f : X ⟶ Y) (k : Y ⟶ Z)
    [LocallyOfFinitePresentation f] [IsOpenImmersion k] :
    (f ≫ k).smoothLocus = f.smoothLocus := by
  ext x
  change ((f ≫ k).stalkMap x).hom.FormallySmooth ↔ (f.stalkMap x).hom.FormallySmooth
  rw [Scheme.Hom.stalkMap_comp]
  exact RingHom.FormallySmooth.respectsIso.cancel_left_isIso (k.stalkMap (f.base x)) (f.stalkMap x)

theorem smoothLocus_le_preimage_of_isPullback_of_isAffine
    {X Y X' Y' : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (h : IsPullback g' f' f g) [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation f'] [Flat g] :
    f'.smoothLocus ≤ g' ⁻¹ᵁ f.smoothLocus := by
  intro x' hx'
  haveI : IsAffine X' := .of_isPullback h

  letI algB := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI algA' := (g.appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI algC := (f'.appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI algBC := (g'.appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI algAC : Algebra Γ(Y, ⊤) Γ(X', ⊤) := (f.appLE ⊤ ⊤ le_top ≫ g'.appLE ⊤ ⊤ le_top).hom.toAlgebra
  haveI : IsScalarTower Γ(Y, ⊤) Γ(X, ⊤) Γ(X', ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have hPO : IsPushout f.appTop g.appTop g'.appTop f'.appTop := isPushout_appTop_of_isPullback h
  have eT : ∀ {S T : Scheme.{u}} (k : S ⟶ T), k.appLE ⊤ ⊤ le_top = k.appTop :=
    fun k => (Scheme.Hom.app_eq_appLE k).symm
  have hw : f.appLE ⊤ ⊤ le_top ≫ g'.appLE ⊤ ⊤ le_top = g.appLE ⊤ ⊤ le_top ≫ f'.appLE ⊤ ⊤ le_top := by
    simp only [eT]; exact hPO.w
  haveI : IsScalarTower Γ(Y, ⊤) Γ(Y', ⊤) Γ(X', ⊤) :=
    IsScalarTower.of_algebraMap_eq' (by
      show (f.appLE ⊤ ⊤ le_top ≫ g'.appLE ⊤ ⊤ le_top).hom = _
      rw [hw]; rfl)
  haveI : Algebra.IsPushout Γ(Y, ⊤) Γ(Y', ⊤) Γ(X, ⊤) Γ(X', ⊤) := by
    refine Algebra.IsPushout.symm ?_
    refine CommRingCat.isPushout_iff_isPushout.mp ?_
    show IsPushout (f.appLE ⊤ ⊤ le_top) (g.appLE ⊤ ⊤ le_top) (g'.appLE ⊤ ⊤ le_top) (f'.appLE ⊤ ⊤ le_top)
    simpa only [eT] using hPO
  haveI : Algebra.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) :=
    f.finitePresentation_appLE (isAffineOpen_top Y) (isAffineOpen_top X) le_top
  haveI : Module.Flat Γ(Y, ⊤) Γ(Y', ⊤) := g.flat_appLE (isAffineOpen_top Y) (isAffineOpen_top Y') le_top

  have hs := (formallySmooth_stalkMap_iff (f := f') ⊤ (isAffineOpen_top Y') ⊤ (isAffineOpen_top X') le_top
    (Set.mem_univ x')).mp hx'

  have key := isSmoothAt_comap_of_isSmoothAt_of_isPushout (A := Γ(Y, ⊤)) (B := Γ(X, ⊤)) (A' := Γ(Y', ⊤))
    (C := Γ(X', ⊤)) (((isAffineOpen_top X').primeIdealOf ⟨x', Set.mem_univ x'⟩).asIdeal) hs

  apply (formallySmooth_stalkMap_iff (f := f) ⊤ (isAffineOpen_top Y) ⊤ (isAffineOpen_top X) le_top
    (Set.mem_univ _)).mpr
  have hcomap := IsAffineOpen.comap_primeIdealOf_appLE (f := g') ⊤ (isAffineOpen_top X) ⊤ (isAffineOpen_top X')
    le_top (Set.mem_univ x')
  exact (isSmoothAt_congr (congrArg PrimeSpectrum.asIdeal hcomap)).mp key

private theorem _root_.AlgebraicGeometry.Scheme.Hom.smoothLocus_le_preimage_of_isPullback
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (h : IsPullback g' f' f g) [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation f'] [Flat g] :
    f'.smoothLocus ≤ g' ⁻¹ᵁ f.smoothLocus := by
  intro x' hx'

  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base (g'.base x'))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show g'.base x' ∈ f ⁻¹ᵁ U from hyU)
      (U.2.preimage f.continuous)
  have hy' : g.base (f'.base x') ∈ U := by
    have := congr($(h.w).base x')
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    rwa [← this]
  obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hU'U⟩ :=
    Y'.isBasis_affineOpens.exists_subset_of_mem_open (show f'.base x' ∈ g ⁻¹ᵁ U from hy')
      (U.2.preimage g.continuous)
  have hsq := Scheme.Hom.isPullback_resLE h hU'U hVU (UY := g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ U') rfl
  haveI : IsAffine U := hU
  haveI : IsAffine V := hV
  haveI : IsAffine U' := hU'
  have hxW : x' ∈ g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ U' := ⟨hxV, hxU'⟩
  have key := smoothLocus_le_preimage_of_isPullback_of_isAffine hsq

  have h1 : (⟨x', hxW⟩ : ↥(g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ U')) ∈
      (f'.resLE U' (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ U') (by simp)).smoothLocus := by
    rw [← smoothLocus_comp_of_isOpenImmersion _ (Scheme.Opens.ι _),
      smoothLocus_congr (Scheme.Hom.resLE_comp_ι ..), ← Scheme.Hom.preimage_smoothLocus_eq]
    exact hx'
  have h2 := key h1

  rw [← smoothLocus_comp_of_isOpenImmersion _ (Scheme.Opens.ι _),
    smoothLocus_congr (Scheme.Hom.resLE_comp_ι ..), ← Scheme.Hom.preimage_smoothLocus_eq,
    ← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage] at h2
  exact h2

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Hom_smoothLocus_le_preimage_of_isPullback.AlgebraicGeometry.Scheme.Hom.smoothLocus_le_preimage_of_isPullback" "AlgebraicGeometry.Scheme.Hom.smoothLocus_le_preimage_of_isPullback"
end AlgebraicGeometry.SmoothLocusBC

theorem solution
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (h : IsPullback g' f' f g) [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation f'] [Flat g] :
    f'.smoothLocus ≤ g' ⁻¹ᵁ f.smoothLocus :=
  AlgebraicGeometry.Scheme.Hom.smoothLocus_le_preimage_of_isPullback h

end S_AlgebraicGeometry_Scheme_Hom_smoothLocus_le_preimage_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_smoothLocus_le_preimage_of_isPullback (solution)

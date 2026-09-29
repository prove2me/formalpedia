-- Prove2me | solution 1 for AlgebraicGeometry.isIso_of_forall_isIso_adicThickening_of_isAdicComplete_of_isClosedImmersion_proj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/be94f7b8-a99a-5083-a640-b6b18ddad91d

import Mathlib
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIso_of_forall_isIso_adicThickening_of_isAdicComplete_of_isClosedImmersion_proj

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace FIso

lemma map_mem_smul_top {A : Type*} [CommRing A] {P Q : Type*} [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (g : P →ₗ[A] Q) {I : Ideal A} {p : P}
    (hp : p ∈ (I • ⊤ : Submodule A P)) : g p ∈ (I • ⊤ : Submodule A Q) := by
  have := Submodule.mem_map_of_mem (f := g) hp
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

theorem exists_away_map_bijective {R C D : Type u} [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [IsNoetherianRing C] (φ : C →+* D) (hφ : φ.Finite) (I : Ideal R)
    (hinj : ∀ (n : ℕ) (c : C), φ c ∈ (I ^ (n + 1)).map (φ.comp (algebraMap R C)) →
      c ∈ (I ^ (n + 1)).map (algebraMap R C))
    (hsurj : ∀ d : D, ∃ c : C, d - φ c ∈ I.map (φ.comp (algebraMap R C)))
    (𝔮 : Ideal C) [𝔮.IsPrime] (h𝔮 : I.map (algebraMap R C) ≤ 𝔮) :
    ∃ s : C, s ∉ 𝔮 ∧ ∀ (Cₛ Dₛ : Type u) [CommRing Cₛ] [CommRing Dₛ] [Algebra C Cₛ] [Algebra D Dₛ]
      [IsLocalization.Away s Cₛ] [IsLocalization.Away (φ s) Dₛ],
      Function.Bijective (IsLocalization.Away.map Cₛ Dₛ φ s) := by
  letI : Algebra C D := φ.toAlgebra
  haveI : Module.Finite C D := hφ
  have hφalg : algebraMap C D = φ := rfl
  set J : Ideal C := I.map (algebraMap R C) with hJ

  have hK : ∃ sK : C, sK - 1 ∈ J ∧ ∀ k : C, φ k = 0 → sK * k = 0 := by
    let K : Ideal C := RingHom.ker φ
    have hKfg : K.FG := IsNoetherian.noetherian K
    have hKle : K ≤ J • K := by
      intro k hk
      have hkJ : k ∈ (⨅ i : ℕ, J ^ i • ⊤ : Submodule C C) := by
        rw [Submodule.mem_iInf]
        intro i
        rw [Ideal.smul_eq_mul, Ideal.mul_top]
        cases i with
        | zero => simp
        | succ n =>
          have := hinj n k (by rw [RingHom.mem_ker.mp hk]; exact zero_mem _)
          rwa [Ideal.map_pow] at this
      obtain ⟨r, hr⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff J k).mp hkJ
      rw [← hr]
      exact Submodule.smul_mem_smul r.2 hk
    obtain ⟨sK, h1, h2⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J K hKfg hKle
    exact ⟨sK, h1, fun k hk => h2 k hk⟩

  have hQ : ∃ sQ : C, sQ - 1 ∈ J ∧ ∀ d : D, ∃ b : C, φ b = φ sQ * d := by
    let P : Submodule C D := LinearMap.range (Algebra.linearMap C D)
    have hfg : (⊤ : Submodule C (D ⧸ P)).FG := Module.Finite.fg_top
    have hle : (⊤ : Submodule C (D ⧸ P)) ≤ J • ⊤ := by
      rintro q -
      obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective P q
      obtain ⟨c, hc⟩ := hsurj d
      have h0 : P.mkQ (φ c) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact ⟨c, rfl⟩
      have h1 : P.mkQ d = P.mkQ (d - φ c) := by rw [map_sub, h0, sub_zero]
      rw [h1]
      have h2 : d - φ c ∈ (J • ⊤ : Submodule C D) := by
        rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, hJ, Ideal.map_map, hφalg]
        exact hc
      exact map_mem_smul_top P.mkQ h2
    obtain ⟨sQ, h1, h2⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J ⊤ hfg hle
    refine ⟨sQ, h1, fun d => ?_⟩
    have h3 : P.mkQ (sQ • d) = 0 := by rw [map_smul, h2 _ Submodule.mem_top]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h3
    obtain ⟨b, hb⟩ := h3
    refine ⟨b, ?_⟩
    rw [Algebra.linearMap_apply, hφalg, Algebra.smul_def, hφalg] at hb
    exact hb
  obtain ⟨sK, hK1, hK2⟩ := hK
  obtain ⟨sQ, hQ1, hQ2⟩ := hQ
  have hnot : ∀ t : C, t - 1 ∈ J → t ∉ 𝔮 := fun t ht htq => by
    have : (1 : C) ∈ 𝔮 := by
      have := 𝔮.sub_mem htq (h𝔮 ht)
      rwa [sub_sub_cancel] at this
    exact (Ideal.ne_top_iff_one 𝔮).mp (Ideal.IsPrime.ne_top ‹_›) this
  refine ⟨sK * sQ, ?_, ?_⟩
  · exact fun h => ((Ideal.IsPrime.mem_or_mem ‹_› h).elim (hnot sK hK1) (hnot sQ hQ1))
  · intro Cₛ Dₛ _ _ _ _ _ _
    refine ⟨(IsLocalization.Away.map_injective_iff Dₛ φ (sK * sQ)).mpr ?_,
      (IsLocalization.Away.map_surjective_iff Cₛ Dₛ φ (sK * sQ)).mpr ?_⟩
    · intro a ha
      exact ⟨1, by rw [pow_one, mul_comm sK sQ, mul_assoc, hK2 a ha, mul_zero]⟩
    · intro a
      obtain ⟨b, hb⟩ := hQ2 a
      exact ⟨sK * b, 1, by rw [pow_one, map_mul, hb, map_mul, mul_assoc]⟩

end FIso

namespace FISO

theorem isProper_of_comp_eq
    {R : Type u} [CommRing R] {Γ X : Scheme.{u}} (γ : Γ ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ιΓ : Γ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hιΓ : IsClosedImmersion ιΓ)
    (hιΓγ : ιΓ ≫ ProjSpace.π R N = γ)
    (N' : ℕ) (ιX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)) (hιX : IsClosedImmersion ιX)
    (hιXf : ιX ≫ ProjSpace.π R N' = f)
    (ψ : Γ ⟶ X) (hψ : ψ ≫ f = γ) : IsProper ψ := by
  have hγ : IsProper γ := by rw [← hιΓγ]; infer_instance
  have hf : IsProper f := by rw [← hιXf]; infer_instance
  have : IsProper (ψ ≫ f) := by rw [hψ]; exact hγ
  exact IsProper.of_comp ψ f

theorem opens_eq_top_of_forall_le_asIdeal_mem
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f] (U : X.Opens)
    (hU : ∀ x : X, I ≤ (f x).asIdeal → x ∈ U) : U = ⊤ := by
  by_contra hne
  obtain ⟨z, hz⟩ : ∃ z : X, z ∉ (U : Set X) := by
    by_contra h
    push Not at h
    exact hne (top_unique fun x _ => h x)
  have hc : IsClosed (f '' (U : Set X)ᶜ) := f.isClosedMap _ U.isOpen.isClosed_compl
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (f z).asIdeal (f z).isPrime.ne_top
  let m' : PrimeSpectrum R := ⟨m, hm.isPrime⟩
  have hspec : f.base z ⤳ m' := (PrimeSpectrum.le_iff_specializes (f z) m').mp hle
  have hm'mem : m' ∈ f '' (U : Set X)ᶜ := hspec.mem_closed hc ⟨z, hz, rfl⟩
  obtain ⟨z', hz', hfz'⟩ := hm'mem
  have hIm : I ≤ (f z').asIdeal := by
    rw [hfz']
    exact hI.trans (sInf_le ⟨bot_le, hm⟩)
  exact hz' (hU z' hIm)

theorem isPullback_adicThickening
    {R : Type u} [CommRing R] (I : Ideal R) {Γ X : Scheme.{u}}
    (γ : Γ ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R)) (ψ : Γ ⟶ X) (hψ : ψ ≫ f = γ) (n : ℕ)
    (ψn : adicThickening γ I n ⟶ adicThickening f I n)
    (hψn : ψn ≫ adicThickeningι f I n = adicThickeningι γ I n ≫ ψ)
    (hψn' : ψn ≫ adicThickeningToBase f I n = adicThickeningToBase γ I n) :
    IsPullback ψn (adicThickeningι γ I n) (adicThickeningι f I n) ψ := by
  have t : IsPullback (adicThickeningToBase f I n) (adicThickeningι f I n) (adicThickeningBase I n) f :=
    (IsPullback.of_hasPullback f (adicThickeningBase I n)).flip
  have s : IsPullback (ψn ≫ adicThickeningToBase f I n) (adicThickeningι γ I n) (adicThickeningBase I n) (ψ ≫ f) := by
    rw [hψn', hψ]
    exact (IsPullback.of_hasPullback γ (adicThickeningBase I n)).flip
  exact IsPullback.of_right s hψn t

theorem mem_range_adicThickeningι_zero_iff
    {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    x ∈ Set.range (adicThickeningι f I 0) ↔ I ≤ (f x).asIdeal := by
  delta adicThickeningι adicThickening
  rw [Scheme.Pullback.range_fst, Set.mem_preimage]
  have : Set.range (adicThickeningBase I 0) = PrimeSpectrum.zeroLocus (I : Set R) := by
    show Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (0 + 1)))) = _
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, zero_add, pow_one]
  rw [this]
  exact (PrimeSpectrum.mem_zeroLocus (f x) (I : Set R)).trans SetLike.coe_subset_coe

theorem subsingleton_preimage_singleton
    {R : Type u} [CommRing R] (I : Ideal R) {Γ X : Scheme.{u}}
    (γ : Γ ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R)) (ψ : Γ ⟶ X) (hψ : ψ ≫ f = γ)
    (ψ0 : adicThickening γ I 0 ⟶ adicThickening f I 0)
    (hψ0 : ψ0 ≫ adicThickeningι f I 0 = adicThickeningι γ I 0 ≫ ψ)
    (hinj : Function.Injective ψ0)
    (x : X) (hx : I ≤ (f x).asIdeal) : (ψ.base ⁻¹' {x}).Subsingleton := by
  intro p hp p' hp'
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hp hp'
  have hpr : ∀ q : Γ, ψ q = x → q ∈ Set.range (adicThickeningι γ I 0) := fun q hq => by
    rw [mem_range_adicThickeningι_zero_iff, ← hψ, Scheme.Hom.comp_apply, hq]
    exact hx
  obtain ⟨q, rfl⟩ := hpr p hp
  obtain ⟨q', rfl⟩ := hpr p' hp'
  have e : (adicThickeningι f I 0) (ψ0 q) = (adicThickeningι f I 0) (ψ0 q') := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hψ0, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hp, hp']
  have e2 := (adicThickeningι f I 0).isClosedEmbedding.injective e
  rw [hinj e2]

theorem finite_preimage_singleton
    {R : Type u} [CommRing R] (I : Ideal R) {Γ X : Scheme.{u}}
    (γ : Γ ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R)) (ψ : Γ ⟶ X) (hψ : ψ ≫ f = γ)
    (ψ0 : adicThickening γ I 0 ⟶ adicThickening f I 0)
    (hψ0 : ψ0 ≫ adicThickeningι f I 0 = adicThickeningι γ I 0 ≫ ψ) (hiso : IsIso ψ0)
    (x : X) (hx : I ≤ (f x).asIdeal) : (ψ.base ⁻¹' {x}).Finite :=
  (subsingleton_preimage_singleton I γ f ψ hψ ψ0 hψ0 (Scheme.Hom.homeomorph ψ0).injective x hx).finite

theorem exists_isFinite_morphismRestrict_of_isIso_zero
    {R : Type u} [CommRing R] (I : Ideal R) {Γ X : Scheme.{u}}
    (γ : Γ ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R)) (ψ : Γ ⟶ X) (hψ : ψ ≫ f = γ) [IsProper ψ]
    (ψ0 : adicThickening γ I 0 ⟶ adicThickening f I 0)
    (hψ0 : ψ0 ≫ adicThickeningι f I 0 = adicThickeningι γ I 0 ≫ ψ) (hiso : IsIso ψ0)
    (x : X) (hx : I ≤ (f x).asIdeal) : ∃ V : X.Opens, x ∈ V ∧ IsFinite (ψ ∣_ V) :=
  exists_isFinite_morphismRestrict_of_finite_preimage_singleton ψ x
    (finite_preimage_singleton I γ f ψ hψ ψ0 hψ0 hiso x hx)

private theorem _root_.FISO.isIso_of_forall_exists_isIso_morphismRestrict
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    {Γ X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f] (ψ : Γ ⟶ X)
    (h : ∀ x : X, I ≤ (f x).asIdeal → ∃ V : X.Opens, x ∈ V ∧ IsIso (ψ ∣_ V)) : IsIso ψ := by
  let S : Set X.Opens := {V : X.Opens | IsIso (ψ ∣_ V)}
  have htop : (⨆ V : S, (V : X.Opens)) = ⊤ :=
    opens_eq_top_of_forall_le_asIdeal_mem I hI f _ (fun x hx => by
      obtain ⟨V, hxV, hV⟩ := h x hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩)
  have H : (MorphismProperty.isomorphisms Scheme) ψ :=
    IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) (fun V : S => (V : X.Opens)) htop
      (fun V => (MorphismProperty.isomorphisms.iff _).mpr V.2)
  exact (MorphismProperty.isomorphisms.iff _).mp H

p2m_export "FISO" "isIso_of_forall_exists_isIso_morphismRestrict"
end FISO

namespace FISO2

theorem surjective_and_ker_of_isPushout {A B C P : CommRingCat.{u}} {a : A ⟶ B} {b : A ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout a b inl inr) (hb : Function.Surjective b.hom) :
    Function.Surjective inl.hom ∧ RingHom.ker inl.hom = (RingHom.ker b.hom).map a.hom := by
  set K : Ideal B := (RingHom.ker b.hom).map a.hom with hKdef
  have hw : ∀ r : A, inl.hom (a.hom r) = inr.hom (b.hom r) := fun r => by
    have := congrArg (fun φ : A ⟶ P => φ.hom r) h.w
    simpa using this
  have hK : ∀ x ∈ K, inl.hom x = 0 := by
    intro x hx
    have : K ≤ RingHom.ker inl.hom := by
      rw [hKdef, Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, hw, RingHom.mem_ker.mp hr, map_zero]
    exact this hx

  let j : A →+* (B ⧸ K) := (Ideal.Quotient.mk K).comp a.hom
  have hj : RingHom.ker b.hom ≤ RingHom.ker j := by
    intro r hr
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hr
  let jC : C →+* (B ⧸ K) :=
    (b.hom.liftOfRightInverse (Function.surjInv hb) (Function.rightInverse_surjInv hb)) ⟨j, hj⟩
  have hjC : ∀ r : A, jC (b.hom r) = j r := fun r =>
    RingHom.liftOfRightInverse_comp_apply b.hom (Function.surjInv hb) (Function.rightInverse_surjInv hb) ⟨j, hj⟩ r
  have hcomm : a ≫ CommRingCat.ofHom (Ideal.Quotient.mk K) = b ≫ CommRingCat.ofHom jC := by
    ext r
    show Ideal.Quotient.mk K (a.hom r) = jC (b.hom r)
    rw [hjC]; rfl
  let u : P ⟶ CommRingCat.of (B ⧸ K) := h.desc (CommRingCat.ofHom (Ideal.Quotient.mk K)) (CommRingCat.ofHom jC) hcomm
  have hu' : inl ≫ u = CommRingCat.ofHom (Ideal.Quotient.mk K) :=
    h.inl_desc (CommRingCat.ofHom (Ideal.Quotient.mk K)) (CommRingCat.ofHom jC) hcomm
  have hu : ∀ x : B, u.hom (inl.hom x) = Ideal.Quotient.mk K x := fun x => by
    have := congrArg (fun φ : B ⟶ CommRingCat.of (B ⧸ K) => φ.hom x) hu'
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  let v : (B ⧸ K) →+* P := Ideal.Quotient.lift K inl.hom hK
  have hv : ∀ x : B, v (Ideal.Quotient.mk K x) = inl.hom x := fun x => rfl
  have huv : u ≫ CommRingCat.ofHom v = 𝟙 P := by
    apply h.hom_ext
    · ext x
      show v (u.hom (inl.hom x)) = inl.hom x
      rw [hu, hv]
    · ext c
      obtain ⟨r, rfl⟩ := hb c
      show v (u.hom (inr.hom (b.hom r))) = inr.hom (b.hom r)
      rw [← hw, hu, hv]
  refine ⟨?_, ?_⟩
  · intro p
    have hp : v (u.hom p) = p := by
      have := congrArg (fun φ : P ⟶ P => φ.hom p) huv
      simpa using this
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u.hom p)
    refine ⟨x, ?_⟩
    rw [← hp, ← hx, hv]
  · apply le_antisymm
    · intro x hx
      have h1 := hu x
      rw [RingHom.mem_ker.mp hx, map_zero] at h1
      exact Ideal.Quotient.eq_zero_iff_mem.mp h1.symm
    · exact fun x hx => hK x hx

theorem surjective_and_ker_appTop_SpecMap_mk {R : Type u} [CommRing R] (J : Ideal R) :
    Function.Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom ∧
    RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom =
      J.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
  have nat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have e : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv := by
    rw [← Category.assoc, ← nat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e' : ∀ x, (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom x =
      (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv.hom
        (Ideal.Quotient.mk J ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x)) := fun x => by
    rw [e]; rfl
  have hinvR : ∀ y : R, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom y) = y := fun y => by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
  have hinvR' : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = x := fun x => by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  have hinjS : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).symm.commRingCatIsoToRingEquiv.injective
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨z, hz⟩ := (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).symm.commRingCatIsoToRingEquiv.surjective y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r, ?_⟩
    rw [e', hinvR]
    exact hz
  · ext x
    rw [RingHom.mem_ker, e']
    constructor
    · intro hx
      have h0 : Ideal.Quotient.mk J ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = 0 :=
        hinjS (hx.trans (map_zero _).symm)
      rw [Ideal.Quotient.eq_zero_iff_mem] at h0
      rw [← hinvR' x]
      exact Ideal.mem_map_of_mem _ h0
    · intro hx
      suffices h0 : Ideal.Quotient.mk J ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = 0 by
        rw [h0, map_zero]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have : J.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ≤
          J.comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom := by
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        rw [Ideal.mem_comap, Ideal.mem_comap, hinvR]
        exact hr
      exact this hx

theorem thickening_appLE_surjective_and_ker
    {R : Type u} [CommRing R] (I : Ideal R) {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (V : Y.Opens) (hV : IsAffineOpen V) (W : (adicThickening g I n).Opens)
    (hW : W = (adicThickeningι g I n) ⁻¹ᵁ V ⊓ (adicThickeningToBase g I n) ⁻¹ᵁ ⊤)
    (hle : W ≤ (adicThickeningι g I n) ⁻¹ᵁ V) :
    Function.Surjective ((adicThickeningι g I n).appLE V W hle).hom ∧
    RingHom.ker ((adicThickeningι g I n).appLE V W hle).hom =
      (I ^ (n + 1)).map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appLE ⊤ V le_top).hom := by
  have H : IsPullback (adicThickeningι g I n) (adicThickeningToBase g I n) g (adicThickeningBase I n) :=
    IsPullback.of_hasPullback _ _
  have hUST : (⊤ : (Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))).Opens) ≤ (adicThickeningBase I n) ⁻¹ᵁ ⊤ := le_top
  have hUSX : V ≤ g ⁻¹ᵁ ⊤ := le_top
  have hps := (isIso_pushoutSection_iff H hUST hUSX hW).mp
    (isIso_pushoutSection_of_isAffineOpen H hUST hUSX hW (isAffineOpen_top _) (isAffineOpen_top _) hV)

  have hb := surjective_and_ker_appTop_SpecMap_mk (I ^ (n + 1))
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at hb
  have hb' : Function.Surjective ((adicThickeningBase I n).appLE ⊤ ⊤ hUST).hom ∧
      RingHom.ker ((adicThickeningBase I n).appLE ⊤ ⊤ hUST).hom =
        (I ^ (n + 1)).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    hb
  obtain ⟨hs, hk⟩ := surjective_and_ker_of_isPushout hps hb'.1
  refine ⟨hs, ?_⟩
  rw [hk, hb'.2, Ideal.map_map, CommRingCat.hom_comp]

theorem quotientMap_bijective_of_square {D C DX CΓ : Type u} [CommRing D] [CommRing C] [CommRing DX]
    [CommRing CΓ] (φ : D →+* C) (πX : D →+* DX) (πΓ : C →+* CΓ) (β : DX →+* CΓ)
    (hsq : πΓ.comp φ = β.comp πX) (hX : Function.Surjective πX) (hβ : Function.Bijective β)
    (J : Ideal D) (hJ : RingHom.ker πX = J) (hJ' : RingHom.ker πΓ = J.map φ) :
    Function.Bijective (Ideal.quotientMap (J.map φ) φ Ideal.le_comap_map) := by
  constructor
  · rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro q hq
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, ← hJ', RingHom.mem_ker] at hq
    have h1 : β (πX d) = 0 := by rw [← RingHom.comp_apply, ← hsq, RingHom.comp_apply, hq]
    have h2 : πX d = 0 := hβ.1 (h1.trans (map_zero β).symm)
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hJ]
    exact h2
  · intro q
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨e, he⟩ := hβ.2 (πΓ c)
    obtain ⟨d, rfl⟩ := hX e
    refine ⟨Ideal.Quotient.mk J d, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, ← hJ', RingHom.mem_ker, map_sub, sub_eq_zero,
      ← RingHom.comp_apply, hsq, RingHom.comp_apply, he]

end FISO2

namespace FIsoGlueStub

variable {R : Type u} [CommRing R] (I : Ideal R) {Γ X : Scheme.{u}}
  (γ : Γ ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R)) (ψ : Γ ⟶ X) (hψ : ψ ≫ f = γ)
  (ψn : ∀ n : ℕ, adicThickening γ I n ⟶ adicThickening f I n)
  (hψn : ∀ n : ℕ, ψn n ≫ adicThickeningι f I n = adicThickeningι γ I n ≫ ψ)
  (hψn' : ∀ n : ℕ, ψn n ≫ adicThickeningToBase f I n = adicThickeningToBase γ I n)

include hψ hψn hψn' in
theorem preimage_singleton_eq_of_isIso_zero [IsIso (ψn 0)] (x : X) (hx : I ≤ (f.base x).asIdeal) :
    ∃ y : Γ, ψ.base ⁻¹' {x} = {y} := by
  have _u := hψn'
  obtain ⟨x0, hx0⟩ := (FISO.mem_range_adicThickeningι_zero_iff I f x).mpr hx
  obtain ⟨q, hq⟩ : ∃ q, (ψn 0) q = x0 := (Scheme.Hom.homeomorph (ψn 0)).surjective x0
  refine ⟨adicThickeningι γ I 0 q, Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · show ψ (adicThickeningι γ I 0 q) = x
    rw [← Scheme.Hom.comp_apply, ← hψn 0, Scheme.Hom.comp_apply, hq, hx0]
  · intro p hp
    have hsub := FISO.subsingleton_preimage_singleton I γ f ψ hψ (ψn 0) (hψn 0)
      (Scheme.Hom.homeomorph (ψn 0)).injective x hx
    refine hsub hp ?_
    show ψ (adicThickeningι γ I 0 q) = x
    rw [← Scheme.Hom.comp_apply, ← hψn 0, Scheme.Hom.comp_apply, hq, hx0]

include hψ hψn hψn' in
theorem quotientMap_bijective_of_isIso_thickening (n : ℕ) [IsIso (ψn n)] (U : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen (ψ ⁻¹ᵁ U)) :
    Function.Bijective (Ideal.quotientMap
      (((I ^ (n + 1)).map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top).hom).map
        (ψ.appLE U (ψ ⁻¹ᵁ U) le_rfl).hom)
      (ψ.appLE U (ψ ⁻¹ᵁ U) le_rfl).hom Ideal.le_comap_map) := by
  subst hψ

  obtain ⟨UX, hUX⟩ : ∃ UX : (adicThickening f I n).Opens,
      UX = (adicThickeningι f I n) ⁻¹ᵁ U ⊓ (adicThickeningToBase f I n) ⁻¹ᵁ ⊤ := ⟨_, rfl⟩
  have hleX : UX ≤ (adicThickeningι f I n) ⁻¹ᵁ U := by rw [hUX]; exact inf_le_left
  obtain ⟨hsX, hkX⟩ := FISO2.thickening_appLE_surjective_and_ker I f n U hU UX hUX hleX

  have hW : (ψn n) ⁻¹ᵁ UX = (adicThickeningι (ψ ≫ f) I n) ⁻¹ᵁ (ψ ⁻¹ᵁ U) ⊓
      (adicThickeningToBase (ψ ≫ f) I n) ⁻¹ᵁ ⊤ := by
    rw [hUX]
    ext x
    show (ψn n) x ∈ ((adicThickeningι f I n) ⁻¹ᵁ U ⊓ (adicThickeningToBase f I n) ⁻¹ᵁ ⊤) ↔
      x ∈ (adicThickeningι (ψ ≫ f) I n) ⁻¹ᵁ (ψ ⁻¹ᵁ U) ⊓ (adicThickeningToBase (ψ ≫ f) I n) ⁻¹ᵁ ⊤
    simp only [TopologicalSpace.Opens.mem_inf]
    show ((adicThickeningι f I n) ((ψn n) x) ∈ U ∧ (adicThickeningToBase f I n) ((ψn n) x) ∈ (⊤ : (Spec _).Opens)) ↔
      (ψ ((adicThickeningι (ψ ≫ f) I n) x) ∈ U ∧ (adicThickeningToBase (ψ ≫ f) I n) x ∈ (⊤ : (Spec _).Opens))
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hψn n, hψn' n]
  have hleW : (ψn n) ⁻¹ᵁ UX ≤ (adicThickeningι (ψ ≫ f) I n) ⁻¹ᵁ (ψ ⁻¹ᵁ U) := by rw [hW]; exact inf_le_left
  obtain ⟨hsΓ, hkΓ⟩ := FISO2.thickening_appLE_surjective_and_ker I (ψ ≫ f) n (ψ ⁻¹ᵁ U) hV ((ψn n) ⁻¹ᵁ UX) hW hleW

  haveI : IsIso ((ψn n).app UX) := Scheme.Hom.isIso_app (ψn n) UX (fun x _ =>
    ⟨(inv (ψn n)) x, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩)
  have hβ : Function.Bijective ((ψn n).appLE UX ((ψn n) ⁻¹ᵁ UX) le_rfl).hom := by
    rw [← Scheme.Hom.app_eq_appLE]
    exact (asIso ((ψn n).app UX)).commRingCatIsoToRingEquiv.bijective

  have hsq : ψ.appLE U (ψ ⁻¹ᵁ U) le_rfl ≫ (adicThickeningι (ψ ≫ f) I n).appLE (ψ ⁻¹ᵁ U) ((ψn n) ⁻¹ᵁ UX) hleW =
      (adicThickeningι f I n).appLE U UX hleX ≫ (ψn n).appLE UX ((ψn n) ⁻¹ᵁ UX) le_rfl := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [hψn]
  have hsq' := congrArg CommRingCat.Hom.hom hsq
  simp only [CommRingCat.hom_comp] at hsq'

  have hρ : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (ψ ≫ f).appLE ⊤ (ψ ⁻¹ᵁ U) le_top) =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top) ≫ ψ.appLE U (ψ ⁻¹ᵁ U) le_rfl := by
    rw [Category.assoc, Scheme.Hom.appLE_comp_appLE]
  rw [hρ, CommRingCat.hom_comp, ← Ideal.map_map] at hkΓ
  exact FISO2.quotientMap_bijective_of_square _ _ _ _ hsq' hsX hβ _ hkX hkΓ

end FIsoGlueStub

namespace FIsoHost

theorem opens_eq_top_of_forall_mem_of_le {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R)) [UniversallyClosed g] (W : Y.Opens)
    (hW : ∀ y : Y, I ≤ (g.base y).asIdeal → y ∈ W) : W = ⊤ := by
  by_contra hne
  have hZne : ((W : Set Y)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro h
    exact hne (TopologicalSpace.Opens.ext (by rw [h]; rfl))
  have hZc : IsClosed ((W : Set Y)ᶜ) := W.2.isClosed_compl
  have himg : IsClosed (g.base '' (W : Set Y)ᶜ) := g.isClosedMap _ hZc
  obtain ⟨y, hy⟩ := hZne
  obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal (g.base y).asIdeal (g.base y).2.ne_top
  let m' : PrimeSpectrum R := ⟨m, hmax.isPrime⟩
  have hm'T : m' ∈ g.base '' (W : Set Y)ᶜ := by
    have hcl : m' ∈ closure {g.base y} := (PrimeSpectrum.le_iff_mem_closure (g.base y) m').mp hle
    exact himg.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨y, hy, rfl⟩) hcl
  obtain ⟨z, hz, hzm⟩ := hm'T
  have hIm : I ≤ m := by
    intro i hi
    by_contra him
    obtain ⟨b, c, hc, hbc⟩ := hmax.exists_inv him
    have hu : IsUnit (i * (-b) + 1) := Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot I hi) (-b)
    have : i * (-b) + 1 = c := by rw [← hbc]; ring
    rw [this] at hu
    exact hmax.ne_top (Ideal.eq_top_of_isUnit_mem m hc hu)
  exact hz (hW z (by rw [hzm]; exact hIm))

theorem isIso_of_forall_exists_isIso_morphismRestrict {Γ X : Scheme.{u}} (ψ : Γ ⟶ X)
    (W : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ IsIso (ψ ∣_ V)) : IsIso ψ := by
  choose V hxV hV using W
  have hsup : ⨆ x, V x = ⊤ := top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩
  refine (MorphismProperty.isomorphisms.iff ψ).mp
    (IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) V hsup
      fun x => ?_)
  exact (MorphismProperty.isomorphisms.iff _).mpr (hV x)

theorem finite_app {Γ X : Scheme.{u}} (ψ : Γ ⟶ X) [IsFinite ψ] (U : X.Opens) (hU : IsAffineOpen U) :
    (ψ.app U).hom.Finite := by
  have h1 : targetAffineLocally (affineAnd RingHom.Finite) ψ := by
    have := (inferInstance : IsFinite ψ)
    rwa [HasAffineProperty.eq_targetAffineLocally (P := @IsFinite)] at this
  obtain ⟨-, h⟩ := (targetAffineLocally_affineAnd_iff RingHom.finite_respectsIso ψ).mp h1 U hU
  exact h

theorem comap_primeIdealOf_eq {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hxU : x ∈ U) :
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.comap
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top).hom = (f.base x).asIdeal := by
  rw [CommRingCat.hom_comp, ← Ideal.comap_comap]
  have h1 := IsAffineOpen.comap_primeIdealOf_appLE (f := f) (x := x) ⊤ (isAffineOpen_top _) U hU
    le_top hxU
  have h1' := congrArg PrimeSpectrum.asIdeal h1
  rw [PrimeSpectrum.comap_asIdeal] at h1'
  rw [h1']
  have h2 : (Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv).base
      ((isAffineOpen_top (Spec (CommRingCat.of R))).primeIdealOf ⟨f.base x, trivial⟩) = f.base x := by
    have := (isAffineOpen_top (Spec (CommRingCat.of R))).fromSpec_primeIdealOf ⟨f.base x, trivial⟩
    rwa [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  have h3 := congrArg PrimeSpectrum.asIdeal h2
  rw [← h3]
  rfl

theorem mem_basicOpen_iff_not_mem_primeIdealOf {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hxU : x ∈ U) (s : Γ(X, U)) :
    x ∈ X.basicOpen s ↔ s ∉ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
  have h1 := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have : x ∈ X.basicOpen s ↔
      hU.primeIdealOf ⟨x, hxU⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen s := by
    show x ∈ X.basicOpen s ↔ hU.fromSpec.base (hU.primeIdealOf ⟨x, hxU⟩) ∈ (X.basicOpen s)
    rw [h1]
  rw [this, hU.fromSpec_preimage_basicOpen]
  exact PrimeSpectrum.mem_basicOpen _ _

theorem isIso_morphismRestrict_basicOpen {Γ X : Scheme.{u}} (ψ : Γ ⟶ X) (U : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen (ψ ⁻¹ᵁ U)) (s : Γ(X, U))
    (h : haveI := hU.isLocalization_basicOpen s
      haveI := hV.isLocalization_basicOpen (ψ.app U s)
      Function.Bijective (IsLocalization.Away.map Γ(X, X.basicOpen s)
        Γ(Γ, Γ.basicOpen (ψ.app U s)) (ψ.app U).hom s)) :
    IsIso (ψ ∣_ X.basicOpen s) := by
  haveI := hU.isLocalization_basicOpen s
  haveI := hV.isLocalization_basicOpen (ψ.app U s)
  have happ : IsIso (ψ.app (X.basicOpen s)) := by
    rw [IsAffineOpen.app_basicOpen_eq_away_map ψ hU hV s]
    haveI : IsIso (CommRingCat.ofHom (IsLocalization.Away.map Γ(X, X.basicOpen s)
        Γ(Γ, Γ.basicOpen (ψ.app U s)) (ψ.app U).hom s)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr h
    refine IsIso.comp_isIso' inferInstance ?_
    rw [eqToHom_op, eqToHom_map]
    infer_instance
  have hUs : IsAffineOpen (X.basicOpen s) := hU.basicOpen s
  have hVs : IsAffineOpen (ψ ⁻¹ᵁ X.basicOpen s) := by
    rw [Scheme.preimage_basicOpen]
    exact hV.basicOpen _
  have h1 : IsIso (Spec.map (ψ.appLE (X.basicOpen s) (ψ ⁻¹ᵁ X.basicOpen s) le_rfl)) := by
    rw [← Scheme.Hom.app_eq_appLE]
    infer_instance
  have h2 := Scheme.Opens.toSpecΓ_SpecMap_appLE ψ (X.basicOpen s) (ψ ⁻¹ᵁ X.basicOpen s) le_rfl
  haveI : IsIso (X.basicOpen s).toSpecΓ := by
    rw [← hUs.isoSpec_hom]; infer_instance
  haveI : IsIso (ψ ⁻¹ᵁ X.basicOpen s).toSpecΓ := by
    rw [← hVs.isoSpec_hom]; infer_instance
  have h3 : IsIso (ψ.resLE (X.basicOpen s) (ψ ⁻¹ᵁ X.basicOpen s) le_rfl ≫ (X.basicOpen s).toSpecΓ) := by
    rw [← h2]; infer_instance
  have h4 : IsIso (ψ.resLE (X.basicOpen s) (ψ ⁻¹ᵁ X.basicOpen s) le_rfl) :=
    IsIso.of_isIso_comp_right _ (X.basicOpen s).toSpecΓ
  rwa [Scheme.Hom.resLE_eq_morphismRestrict] at h4

end FIsoHost

namespace FIso

theorem quasiFiniteAt_of_preimage_singleton {Γ X : Scheme.{u}} (ψ : Γ ⟶ X) [LocallyOfFiniteType ψ]
    (y : Γ) (h : ψ.base ⁻¹' {ψ.base y} = {y}) : ψ.QuasiFiniteAt y := by
  have hfin : (ψ.base ⁻¹' {ψ.base y}).Finite := by rw [h]; exact Set.finite_singleton y
  have : Finite (ψ.fiber (ψ.base y)) := (ψ.fiberHomeo (ψ.base y)).finite_iff.mpr hfin
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

theorem isIso_main
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {Γ X : Scheme.{u}} (γ : Γ ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ιΓ : Γ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hιΓ : IsClosedImmersion ιΓ)
    (hιΓγ : ιΓ ≫ ProjSpace.π R N = γ)
    (N' : ℕ) (ιX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)) (hιX : IsClosedImmersion ιX)
    (hιXf : ιX ≫ ProjSpace.π R N' = f)
    (ψ : Γ ⟶ X) (hψ : ψ ≫ f = γ)
    (ψn : ∀ n : ℕ, adicThickening γ I n ⟶ adicThickening f I n)
    (hψn : ∀ n : ℕ, ψn n ≫ adicThickeningι f I n = adicThickeningι γ I n ≫ ψ)
    (hψn' : ∀ n : ℕ, ψn n ≫ adicThickeningToBase f I n = adicThickeningToBase γ I n)
    (hiso : ∀ n : ℕ, IsIso (ψn n)) :
    IsIso ψ := by
  haveI := hιΓ
  haveI := hιX
  haveI : IsProper γ := by rw [← hιΓγ]; infer_instance
  haveI : IsProper f := by rw [← hιXf]; infer_instance
  haveI : IsProper ψ := by
    have : IsProper (ψ ≫ f) := by rw [hψ]; infer_instance
    exact IsProper.of_comp ψ f
  haveI : ∀ n, IsIso (ψn n) := hiso
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f

  have hqf : LocallyQuasiFinite ψ := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    apply FIsoHost.opens_eq_top_of_forall_mem_of_le I γ ψ.quasiFiniteLocus
    intro y hy
    show ψ.QuasiFiniteAt y
    have hx : I ≤ (f.base (ψ.base y)).asIdeal := by
      rwa [← Scheme.Hom.comp_apply, hψ]
    obtain ⟨y', hy'⟩ :=
      FIsoGlueStub.preimage_singleton_eq_of_isIso_zero I γ f ψ hψ ψn hψn hψn' (ψ.base y) hx
    have hyy : y' = y := by
      have : y ∈ ψ.base ⁻¹' {ψ.base y} := rfl
      rw [hy'] at this
      exact (Set.mem_singleton_iff.mp this).symm
    exact quasiFiniteAt_of_preimage_singleton ψ y (hyy ▸ hy')
  haveI : IsFinite ψ := IsFinite.of_isProper_of_locallyQuasiFinite ψ

  have hloc : ∀ x : X, I ≤ (f.base x).asIdeal → ∃ V : X.Opens, x ∈ V ∧ IsIso (ψ ∣_ V) := by
    intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hV : IsAffineOpen (ψ ⁻¹ᵁ U) := hU.preimage ψ
    let ρ : CommRingCat.of R ⟶ Γ(X, U) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top
    let φ : Γ(X, U) ⟶ Γ(Γ, ψ ⁻¹ᵁ U) := ψ.app U
    have hφ : ψ.appLE U (ψ ⁻¹ᵁ U) le_rfl = φ := (Scheme.Hom.app_eq_appLE ψ).symm
    letI : Algebra R Γ(X, U) := ρ.hom.toAlgebra
    have hρ : algebraMap R Γ(X, U) = ρ.hom := rfl
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have hbij : ∀ n : ℕ, Function.Bijective (Ideal.quotientMap (((I ^ (n + 1)).map ρ.hom).map φ.hom) φ.hom
        Ideal.le_comap_map) := fun n => by
      have := FIsoGlueStub.quotientMap_bijective_of_isIso_thickening I γ f ψ hψ ψn hψn hψn' n U hU hV
      rw [hφ] at this
      exact this
    have hinj : ∀ (n : ℕ) (c : Γ(X, U)), φ.hom c ∈ (I ^ (n + 1)).map (φ.hom.comp (algebraMap R _)) →
        c ∈ (I ^ (n + 1)).map (algebraMap R Γ(X, U)) := by
      intro n c hc
      have h1 : Ideal.quotientMap (((I ^ (n + 1)).map ρ.hom).map φ.hom) φ.hom Ideal.le_comap_map
          (Ideal.Quotient.mk ((I ^ (n + 1)).map ρ.hom) c) = 0 := by
        rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.map_map]
        exact hc
      have h2 := (hbij n).1 (h1.trans (map_zero _).symm)
      exact Ideal.Quotient.eq_zero_iff_mem.mp h2
    have hsurj : ∀ d : Γ(Γ, ψ ⁻¹ᵁ U), ∃ c : Γ(X, U),
        d - φ.hom c ∈ I.map (φ.hom.comp (algebraMap R Γ(X, U))) := by
      intro d
      obtain ⟨c', hc'⟩ := (hbij 0).2 (Ideal.Quotient.mk _ d)
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
      refine ⟨c, ?_⟩
      rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, zero_add, pow_one, Ideal.map_map] at hc'
      rw [← neg_sub]
      exact Submodule.neg_mem _ hc'
    set 𝔮 := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal with h𝔮def
    have h𝔮 : I.map (algebraMap R Γ(X, U)) ≤ 𝔮 := by
      rw [Ideal.map_le_iff_le_comap, hρ, h𝔮def, FIsoHost.comap_primeIdealOf_eq f U hU x hxU]
      exact hx
    obtain ⟨s, hs𝔮, hs⟩ :=
      exists_away_map_bijective φ.hom (FIsoHost.finite_app ψ U hU) I hinj hsurj 𝔮 h𝔮
    refine ⟨X.basicOpen s, (FIsoHost.mem_basicOpen_iff_not_mem_primeIdealOf U hU x hxU s).mpr hs𝔮,
      FIsoHost.isIso_morphismRestrict_basicOpen ψ U hU hV s ?_⟩
    haveI := hU.isLocalization_basicOpen s
    haveI := hV.isLocalization_basicOpen (ψ.app U s)
    exact hs Γ(X, X.basicOpen s) Γ(Γ, Γ.basicOpen (ψ.app U s))

  let W : X.Opens := ⨆ V : {V : X.Opens // IsIso (ψ ∣_ V)}, V.1
  have hW : W = ⊤ := FIsoHost.opens_eq_top_of_forall_mem_of_le I f W (fun x hx => by
    obtain ⟨V, hxV, hV⟩ := hloc x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩)
  apply FIsoHost.isIso_of_forall_exists_isIso_morphismRestrict ψ
  intro x
  have hxW : x ∈ W := by rw [hW]; trivial
  obtain ⟨⟨V, hV⟩, hxV⟩ := TopologicalSpace.Opens.mem_iSup.mp hxW
  exact ⟨V, hxV, hV⟩

end FIso

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {Γ X : Scheme.{u}} (γ : Γ ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ιΓ : Γ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hιΓ : IsClosedImmersion ιΓ)
    (hιΓγ : ιΓ ≫ ProjSpace.π R N = γ)
    (N' : ℕ) (ιX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)) (hιX : IsClosedImmersion ιX)
    (hιXf : ιX ≫ ProjSpace.π R N' = f)
    (ψ : Γ ⟶ X) (hψ : ψ ≫ f = γ)
    (ψn : ∀ n : ℕ, adicThickening γ I n ⟶ adicThickening f I n)
    (hψn : ∀ n : ℕ, ψn n ≫ adicThickeningι f I n = adicThickeningι γ I n ≫ ψ)
    (hψn' : ∀ n : ℕ, ψn n ≫ adicThickeningToBase f I n = adicThickeningToBase γ I n)
    (hiso : ∀ n : ℕ, IsIso (ψn n)) :
    IsIso ψ :=
  FIso.isIso_main I γ f N ιΓ hιΓ hιΓγ N' ιX hιX hιXf ψ hψ ψn hψn hψn' hiso

end S_AlgebraicGeometry_isIso_of_forall_isIso_adicThickening_of_isAdicComplete_of_isClosedImmersion_proj
end P2MW
export P2MW.S_AlgebraicGeometry_isIso_of_forall_isIso_adicThickening_of_isAdicComplete_of_isClosedImmersion_proj (solution)

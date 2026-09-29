-- Prove2me | solution 1 for Algebra.isUnramifiedAt_adicCompletion_of_forall_not_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/456a0904-7a50-56d7-89a6-6444a497e0d0

import Mathlib
import Definitions.Def_AdicCompletionGaloisAction
import Definitions.Def_AdicCompletionTensorRing
import Definitions.Def_SemilocalAdicCompletion
import Theorems.Thm_AdicCompletion_isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_isUnramifiedAt_adicCompletion_of_forall_not_isMaximal
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal"

set_option autoImplicit false

open IsLocalRing
open scoped AdicCompletion.GaloisAction
open scoped TensorProduct

namespace Algebra
p2m_export "Algebra" "TensorProduct.includeRight algebraMap FormallyUnramified algebraMap_self unramifiedLocus_eq_compl_support unramifiedLocus FormallyUnramified.iff_of_equiv restrictScalars IsUnramifiedAt TensorProduct.rightAlgebra"
namespace IsUnramifiedAt
p2m_export "Algebra.IsUnramifiedAt" "comp"
namespace CH1
p2m_open "Algebra.IsUnramifiedAt Algebra"

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]

theorem algebraMap_eq_includeRight :
    algebraMap A (S ⊗[R] A) = (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom :=
  rfl

theorem forall_exists_smul_eq_zero_of_isUnramifiedAt (𝔮 : Ideal A) [𝔮.IsPrime]
    [Algebra.IsUnramifiedAt R 𝔮] : ∀ ω : Ω[A⁄R], ∃ r ∉ 𝔮, r • ω = 0 := by
  have h : (⟨𝔮, inferInstance⟩ : PrimeSpectrum A) ∈ Algebra.unramifiedLocus R A := ‹Algebra.IsUnramifiedAt R 𝔮›
  rw [Algebra.unramifiedLocus_eq_compl_support, Set.mem_compl_iff, Module.notMem_support_iff'] at h
  exact h

theorem isUnramifiedAt_of_forall_exists_smul_eq_zero {T B : Type*} [CommRing T] [CommRing B] [Algebra T B]
    (𝔔 : Ideal B) [𝔔.IsPrime] (h : ∀ ω : Ω[B⁄T], ∃ r ∉ 𝔔, r • ω = 0) : Algebra.IsUnramifiedAt T 𝔔 := by
  have : (⟨𝔔, inferInstance⟩ : PrimeSpectrum B) ∈ Algebra.unramifiedLocus T B := by
    rw [Algebra.unramifiedLocus_eq_compl_support, Set.mem_compl_iff, Module.notMem_support_iff']
    exact h
  exact this

theorem forall_exists_smul_eq_zero_baseChange (𝔔 : Ideal (S ⊗[R] A)) [𝔔.IsPrime]
    (h : ∀ ω : Ω[A⁄R], ∃ r ∉ 𝔔.comap (algebraMap A (S ⊗[R] A)), r • ω = 0) :
    ∀ n : (S ⊗[R] A) ⊗[A] Ω[A⁄R], ∃ t ∉ 𝔔, t • n = 0 := by
  intro n
  induction n using TensorProduct.induction_on with
  | zero => exact ⟨1, fun h1 => ‹𝔔.IsPrime›.ne_top ((Ideal.eq_top_iff_one 𝔔).mpr h1), smul_zero _⟩
  | tmul b ω =>
      obtain ⟨r, hr, hrω⟩ := h ω
      refine ⟨algebraMap A (S ⊗[R] A) r, fun hmem => hr (Ideal.mem_comap.mpr hmem), ?_⟩
      rw [TensorProduct.smul_tmul', algebraMap_smul, TensorProduct.smul_tmul, hrω, TensorProduct.tmul_zero]
  | add x y hx hy =>
      obtain ⟨t₁, ht₁, h₁⟩ := hx
      obtain ⟨t₂, ht₂, h₂⟩ := hy
      refine ⟨t₁ * t₂, fun hmem => (‹𝔔.IsPrime›.mem_or_mem hmem).elim ht₁ ht₂, ?_⟩
      rw [smul_add, mul_smul, mul_smul, h₂, smul_zero, add_zero, smul_comm, h₁, smul_zero]

theorem baseChange (𝔔 : Ideal (S ⊗[R] A)) [𝔔.IsPrime]
    [Algebra.IsUnramifiedAt R (𝔔.comap (algebraMap A (S ⊗[R] A)))] : Algebra.IsUnramifiedAt S 𝔔 := by
  apply isUnramifiedAt_of_forall_exists_smul_eq_zero
  have h2 := forall_exists_smul_eq_zero_baseChange 𝔔
    (forall_exists_smul_eq_zero_of_isUnramifiedAt (R := R) (𝔔.comap (algebraMap A (S ⊗[R] A))))
  have h3 : (⟨𝔔, inferInstance⟩ : PrimeSpectrum (S ⊗[R] A)) ∉
      Module.support (S ⊗[R] A) ((S ⊗[R] A) ⊗[A] Ω[A⁄R]) :=
    Module.notMem_support_iff'.mpr h2
  rw [(KaehlerDifferential.tensorKaehlerEquiv R S A (S ⊗[R] A)).support_eq] at h3
  exact Module.notMem_support_iff'.mp h3

end Algebra.IsUnramifiedAt.CH1

namespace Algebra
p2m_export "Algebra" "TensorProduct.includeRight algebraMap FormallyUnramified algebraMap_self unramifiedLocus_eq_compl_support unramifiedLocus FormallyUnramified.iff_of_equiv restrictScalars IsUnramifiedAt TensorProduct.rightAlgebra"
namespace IsUnramifiedAt
p2m_export "Algebra.IsUnramifiedAt" "comp"
namespace CH2
p2m_open "Algebra.IsUnramifiedAt Algebra"

theorem isLocalization_atPrime_comap {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (𝔓 : Ideal B) [𝔓.IsPrime] :
    IsLocalization.AtPrime (Localization.AtPrime 𝔓) (𝔓.comap (algebraMap A B)) :=
  IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime 𝔓) 𝔓

noncomputable def localizationEquiv (R : Type*) {A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (M : Submonoid A) [IsLocalization M B] (𝔓 : Ideal B) [𝔓.IsPrime] :
    Localization.AtPrime (𝔓.comap (algebraMap A B)) ≃ₐ[R] Localization.AtPrime 𝔓 :=
  haveI := isLocalization_atPrime_comap M 𝔓
  (IsLocalization.algEquiv (𝔓.comap (algebraMap A B)).primeCompl
    (Localization.AtPrime (𝔓.comap (algebraMap A B))) (Localization.AtPrime 𝔓)).restrictScalars R

private theorem _root_.Algebra.IsUnramifiedAt.CH2.iff_comap (R : Type*) {A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (M : Submonoid A) [IsLocalization M B] (𝔓 : Ideal B) [𝔓.IsPrime] :
    Algebra.IsUnramifiedAt R 𝔓 ↔ Algebra.IsUnramifiedAt R (𝔓.comap (algebraMap A B)) :=
  (Algebra.FormallyUnramified.iff_of_equiv (localizationEquiv R M 𝔓)).symm

p2m_export "Algebra.IsUnramifiedAt.CH2" "iff_comap"
end Algebra.IsUnramifiedAt.CH2

namespace UnramCompletion
namespace HYP

theorem isLocalization_atPrime_comap {C S : Type*} [CommRing C] [CommRing S] [Algebra C S]
    (M : Submonoid C) [IsLocalization M S] (𝔔 : Ideal S) [𝔔.IsPrime] :
    IsLocalization.AtPrime (Localization.AtPrime 𝔔) (𝔔.comap (algebraMap C S)) :=
  IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime 𝔔) 𝔔

noncomputable def localizationEquiv (O : Type*) {C S : Type*} [CommRing O] [CommRing C] [CommRing S]
    [Algebra O C] [Algebra C S] [Algebra O S] [IsScalarTower O C S]
    (M : Submonoid C) [IsLocalization M S] (𝔔 : Ideal S) [𝔔.IsPrime] :
    Localization.AtPrime (𝔔.comap (algebraMap C S)) ≃ₐ[O] Localization.AtPrime 𝔔 :=
  haveI := isLocalization_atPrime_comap M 𝔔
  (IsLocalization.algEquiv (𝔔.comap (algebraMap C S)).primeCompl
    (Localization.AtPrime (𝔔.comap (algebraMap C S))) (Localization.AtPrime 𝔔)).restrictScalars O

private theorem _root_.UnramCompletion.HYP.iff_comap (O : Type*) {C S : Type*} [CommRing O] [CommRing C] [CommRing S]
    [Algebra O C] [Algebra C S] [Algebra O S] [IsScalarTower O C S]
    (M : Submonoid C) [IsLocalization M S] (𝔔 : Ideal S) [𝔔.IsPrime] :
    Algebra.IsUnramifiedAt O 𝔔 ↔ Algebra.IsUnramifiedAt O (𝔔.comap (algebraMap C S)) :=
  (Algebra.FormallyUnramified.iff_of_equiv (localizationEquiv O M 𝔔)).symm

p2m_export "UnramCompletion.HYP" "iff_comap"
end UnramCompletion.HYP

namespace UnramCompletion

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem isUnramifiedAt_baseChange_of_comap_includeRight
    {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    (𝔔 : Ideal (S ⊗[R] A)) [𝔔.IsPrime]
    [Algebra.IsUnramifiedAt R
      (𝔔.comap (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom)] :
    Algebra.IsUnramifiedAt S 𝔔 :=
  Algebra.IsUnramifiedAt.CH1.baseChange (R := R) 𝔔

theorem isUnramifiedAt_of_isLocalization_of_comap
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (M : Submonoid A) [IsLocalization M B]
    (𝔓 : Ideal B) [𝔓.IsPrime] [Algebra.IsUnramifiedAt R (𝔓.comap (algebraMap A B))] :
    Algebra.IsUnramifiedAt R 𝔓 :=
  (Algebra.IsUnramifiedAt.CH2.iff_comap R M 𝔓).mpr ‹_›

end UnramCompletion

namespace UnramCompletion

theorem isLocalization_powers_of_surjective {T B : Type*} [CommRing T] [CommRing B] [Algebra T B]
    (e : T) (he : algebraMap T B e = 1) (hsurj : Function.Surjective (algebraMap T B))
    (hker : ∀ x : T, algebraMap T B x = 0 → e * x = 0) :
    IsLocalization (Submonoid.powers e) B where
  map_units y := by
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
    rw [← hn, map_pow, he, one_pow]
    exact isUnit_one
  surj z := by
    obtain ⟨x, hx⟩ := hsurj z
    exact ⟨⟨x, 1⟩, by simp [hx]⟩
  exists_of_eq {x y} h := by
    refine ⟨⟨e, Submonoid.mem_powers e⟩, ?_⟩
    have h0 : algebraMap T B (x - y) = 0 := by rw [map_sub, h, sub_self]
    have := hker _ h0
    rw [mul_sub, sub_eq_zero] at this
    exact this

section Setting

abbrev mC (O : Type) [CommRing O] [IsLocalRing O] (C : Type) [CommRing C] [Algebra O C] : Ideal C :=
  (maximalIdeal O).map (algebraMap O C)

variable (O : Type) [CommRing O] [IsLocalRing O]
  {C : Type} [CommRing C] [Algebra O C]
  (𝔫 : Ideal C) [h𝔫 : 𝔫.LiesOver (maximalIdeal O)]

theorem mC_le : mC O C ≤ 𝔫 := by
  rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, ← h𝔫.over]

theorem isArtinianRing_quot [Module.Finite O C] : IsArtinianRing (C ⧸ mC O C) := by
  letI : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field _
  haveI : Module.Finite O (C ⧸ mC O C) :=
    Module.Finite.of_surjective ((Ideal.Quotient.mkₐ O (mC O C)).toLinearMap)
      (Ideal.Quotient.mkₐ_surjective O (mC O C))
  haveI : Module.Finite (O ⧸ maximalIdeal O) (C ⧸ mC O C) :=
    Module.Finite.of_restrictScalars_finite O (O ⧸ maximalIdeal O) (C ⧸ mC O C)
  exact IsArtinianRing.of_finite (O ⧸ maximalIdeal O) (C ⧸ mC O C)

noncomputable def theta :
    AdicCompletion (maximalIdeal O) O ⊗[O] C →ₐ[O] AdicCompletion 𝔫 C :=
  ((AdicCompletion.semilocalComponent (mC O C) (mC_le O 𝔫)).restrictScalars O).comp
    (AdicCompletion.tensorRingHom C (maximalIdeal O))

theorem theta_tmul (x : AdicCompletion (maximalIdeal O) O) (c : C) :
    theta O 𝔫 (x ⊗ₜ[O] c) =
      AdicCompletion.semilocalComponent (mC O C) (mC_le O 𝔫)
        (AdicCompletion.completionBaseChangeHom C (maximalIdeal O) x *
          AdicCompletion.of (mC O C) C c) := by
  change AdicCompletion.semilocalComponent (mC O C) (mC_le O 𝔫)
    (AdicCompletion.tensorRingHom C (maximalIdeal O) (x ⊗ₜ[O] c)) = _
  rw [AdicCompletion.tensorRingHom_tmul]

theorem theta_one_tmul (c : C) : theta O 𝔫 ((1 : AdicCompletion (maximalIdeal O) O) ⊗ₜ[O] c) =
    AdicCompletion.of 𝔫 C c := by
  rw [theta_tmul, map_one, one_mul, AdicCompletion.semilocalComponent_of]

theorem theta_tmul_one (x : AdicCompletion (maximalIdeal O) O) :
    theta O 𝔫 (x ⊗ₜ[O] (1 : C)) =
      algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) x := by
  have h1 : AdicCompletion.of (mC O C) C (1 : C) = 1 := by
    change algebraMap C (AdicCompletion (mC O C) C) 1 = 1
    exact map_one _
  rw [theta_tmul, h1, mul_one]
  apply AdicCompletion.ext_evalₐ
  intro n
  obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal O) n x)
  rw [AdicCompletion.evalₐ_algebraMap_of_liesOver (maximalIdeal O) 𝔫 n o x ho.symm]
  rw [AdicCompletion.semilocalComponent, AdicCompletion.evalₐ_mapₐ,
    AdicCompletion.completionBaseChangeHom, AdicCompletion.evalₐ_mapₐ, ← ho,
    AdicCompletion.levelMapₐ_mk, AdicCompletion.levelMapₐ_mk]
  rfl

end Setting

section Structure

variable (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  {C : Type} [CommRing C] [Algebra O C] [Module.Finite O C]
  (𝔫 : Ideal C) [𝔫.IsMaximal] [h𝔫 : 𝔫.LiesOver (maximalIdeal O)]

theorem theta_surjective_and_exists_idem :
    Function.Surjective (theta O 𝔫) ∧
      ∃ e : AdicCompletion (maximalIdeal O) O ⊗[O] C, theta O 𝔫 e = 1 ∧
        ∀ x, theta O 𝔫 x = 0 → e * x = 0 := by
  classical
  haveI : IsNoetherianRing C := IsNoetherianRing.of_finite O C
  haveI : IsArtinianRing (C ⧸ mC O C) := isArtinianRing_quot O

  let I : Ideal C := mC O C
  let P₀ : {P : Ideal C // P.IsMaximal ∧ I ≤ P} := ⟨𝔫, ‹𝔫.IsMaximal›, mC_le O 𝔫⟩
  let Φ := AdicCompletion.tensorRingHom C (maximalIdeal O)
  let Ψ := AdicCompletion.semilocalPiEquiv I
  have hΦ : Function.Bijective Φ := AdicCompletion.tensorRingHom_bijective C (maximalIdeal O)

  have hθ : ∀ x, theta O 𝔫 x = Ψ (Φ x) P₀ := by
    intro x
    rfl
  refine ⟨?_, ?_⟩
  · intro z
    obtain ⟨y, hy⟩ := Ψ.surjective (Pi.single P₀ z)
    obtain ⟨x, hx⟩ := hΦ.2 y
    refine ⟨x, ?_⟩
    rw [hθ, hx, hy, Pi.single_eq_same]
  · obtain ⟨ε, hε⟩ := Ψ.surjective (Pi.single P₀ 1)
    obtain ⟨e, he⟩ := hΦ.2 ε
    refine ⟨e, ?_, ?_⟩
    · rw [hθ, he, hε, Pi.single_eq_same]
    · intro x hx
      rw [hθ] at hx
      apply hΦ.1
      rw [map_mul, map_zero, he]
      apply Ψ.injective
      rw [map_mul, map_zero, hε]
      funext P
      rw [Pi.mul_apply, Pi.zero_apply]
      by_cases hP : P = P₀
      · subst hP; rw [hx, mul_zero]
      · rw [Pi.single_eq_of_ne hP, zero_mul]

theorem isLocalization_theta :
    letI := (theta O 𝔫).toRingHom.toAlgebra
    ∃ e : AdicCompletion (maximalIdeal O) O ⊗[O] C,
      IsLocalization (Submonoid.powers e) (AdicCompletion 𝔫 C) := by
  letI := (theta O 𝔫).toRingHom.toAlgebra
  obtain ⟨hsurj, e, he1, hker⟩ := theta_surjective_and_exists_idem O 𝔫
  exact ⟨e, isLocalization_powers_of_surjective e he1 hsurj hker⟩

theorem comap_le_and_ne {C' : Type} [CommRing C'] [IsNoetherianRing C'] (𝔫' : Ideal C') [𝔫'.IsMaximal]
    (𝔭 : Ideal (AdicCompletion 𝔫' C')) [𝔭.IsPrime] (h𝔭 : ¬ 𝔭.IsMaximal) :
    𝔭.comap (algebraMap C' (AdicCompletion 𝔫' C')) ≤ 𝔫' ∧
      𝔭.comap (algebraMap C' (AdicCompletion 𝔫' C')) ≠ 𝔫' := by
  obtain ⟨_, hloc, hmax, -, hcomap, -⟩ :=
    AdicCompletion.isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal 𝔫'
  haveI := hloc
  have hle : 𝔭 ≤ maximalIdeal (AdicCompletion 𝔫' C') :=
    IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  constructor
  · exact (Ideal.comap_mono hle).trans hcomap.le
  · intro heq
    apply h𝔭
    have hge : maximalIdeal (AdicCompletion 𝔫' C') ≤ 𝔭 := by
      rw [hmax, Ideal.map_le_iff_le_comap, heq]
    rw [le_antisymm hle hge]
    exact IsLocalRing.maximalIdeal.isMaximal _

end Structure

theorem isUnramifiedAt_congr {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {I J : Ideal A} [I.IsPrime] [J.IsPrime] (h : I = J) [Algebra.IsUnramifiedAt R J] :
    Algebra.IsUnramifiedAt R I := by
  subst h
  assumption

theorem isUnramifiedAt_of_forall_not_isMaximal_localization
    {O C S : Type} [CommRing O] [CommRing C] [CommRing S]
    [Algebra O C] [Algebra C S] [Algebra O S] [IsScalarTower O C S]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [IsLocalRing S] [IsLocalization.AtPrime S 𝔫]
    (hunr : ∀ (𝔔 : Ideal S) [𝔔.IsPrime], ¬ 𝔔.IsMaximal → Algebra.IsUnramifiedAt O 𝔔)
    (𝔮 : Ideal C) [𝔮.IsPrime] (hle : 𝔮 ≤ 𝔫) (hne : 𝔮 ≠ 𝔫) :
    Algebra.IsUnramifiedAt O 𝔮 := by

  have hdisj : Disjoint (𝔫.primeCompl : Set C) (𝔮 : Set C) :=
    Set.disjoint_left.mpr fun x hx hx' => hx (hle hx')

  set 𝔔 : Ideal S := 𝔮.map (algebraMap C S) with h𝔔
  haveI h𝔔p : 𝔔.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔫.primeCompl S 𝔮 ‹_› hdisj
  have hunder : 𝔔.comap (algebraMap C S) = 𝔮 :=
    IsLocalization.under_map_of_isPrime_disjoint 𝔫.primeCompl S ‹𝔮.IsPrime› hdisj

  have hnm : ¬ 𝔔.IsMaximal := by
    intro hmax
    apply hne
    have h1 : 𝔔 = IsLocalRing.maximalIdeal S := IsLocalRing.eq_maximalIdeal hmax
    have h2 : (IsLocalRing.maximalIdeal S).comap (algebraMap C S) = 𝔫 :=
      IsLocalization.AtPrime.under_maximalIdeal S 𝔫
    rw [← hunder, h1, h2]

  have h := hunr 𝔔 hnm
  have h' := (UnramCompletion.HYP.iff_comap O 𝔫.primeCompl 𝔔).mp h

  revert h'
  have key : ∀ (I : Ideal C) (hI : I.IsPrime), I = 𝔮 →
      (@Algebra.IsUnramifiedAt O C _ _ _ I hI → Algebra.IsUnramifiedAt O 𝔮) := by
    rintro I hI rfl h''
    exact h''
  exact key _ _ hunder

end UnramCompletion

open UnramCompletion in
theorem solution
    {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    {C : Type} [CommRing C] [Algebra O C] [Module.Finite O C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    (S : Type) [CommRing S] [IsLocalRing S] [Algebra C S] [IsLocalization.AtPrime S 𝔫]
    [Algebra O S] [IsScalarTower O C S]
    (hunr : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], ¬ 𝔮.IsMaximal → Algebra.IsUnramifiedAt O 𝔮)
    (𝔭 : Ideal (AdicCompletion 𝔫 C)) [𝔭.IsPrime] (h𝔭 : ¬ 𝔭.IsMaximal) :
    Algebra.IsUnramifiedAt (AdicCompletion (maximalIdeal O) O) 𝔭 := by
  classical
  haveI : IsNoetherianRing C := IsNoetherianRing.of_finite O C

  obtain ⟨hqle, hqne⟩ := comap_le_and_ne 𝔫 𝔭 h𝔭

  haveI hq : Algebra.IsUnramifiedAt O (𝔭.comap (algebraMap C (AdicCompletion 𝔫 C))) :=
    isUnramifiedAt_of_forall_not_isMaximal_localization 𝔫 (S := S) hunr _ hqle hqne

  letI : Algebra (AdicCompletion (maximalIdeal O) O ⊗[O] C) (AdicCompletion 𝔫 C) :=
    (theta O 𝔫).toRingHom.toAlgebra
  haveI : IsScalarTower (AdicCompletion (maximalIdeal O) O)
      (AdicCompletion (maximalIdeal O) O ⊗[O] C) (AdicCompletion 𝔫 C) :=
    IsScalarTower.of_algebraMap_eq (R := AdicCompletion (maximalIdeal O) O)
      (S := AdicCompletion (maximalIdeal O) O ⊗[O] C) (A := AdicCompletion 𝔫 C)
      fun x => (theta_tmul_one O 𝔫 x).symm.trans rfl
  obtain ⟨e, hloc⟩ := isLocalization_theta O 𝔫

  set 𝔔 : Ideal (AdicCompletion (maximalIdeal O) O ⊗[O] C) :=
    𝔭.comap (algebraMap (AdicCompletion (maximalIdeal O) O ⊗[O] C) (AdicCompletion 𝔫 C)) with h𝔔
  have hright : 𝔔.comap (Algebra.TensorProduct.includeRight
      (R := O) (A := AdicCompletion (maximalIdeal O) O) (B := C)).toRingHom =
      𝔭.comap (algebraMap C (AdicCompletion 𝔫 C)) := by
    rw [h𝔔, Ideal.comap_comap]
    congr 1
    refine RingHom.ext fun c => ?_
    change theta O 𝔫 ((1 : AdicCompletion (maximalIdeal O) O) ⊗ₜ[O] c) = _
    rw [theta_one_tmul, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

  haveI : Algebra.IsUnramifiedAt O (𝔔.comap (Algebra.TensorProduct.includeRight
      (R := O) (A := AdicCompletion (maximalIdeal O) O) (B := C)).toRingHom) :=
    isUnramifiedAt_congr hright
  haveI : Algebra.IsUnramifiedAt (AdicCompletion (maximalIdeal O) O) 𝔔 :=
    isUnramifiedAt_baseChange_of_comap_includeRight 𝔔

  exact isUnramifiedAt_of_isLocalization_of_comap (Submonoid.powers e) 𝔭

end S_Algebra_isUnramifiedAt_adicCompletion_of_forall_not_isMaximal
end P2MW
export P2MW.S_Algebra_isUnramifiedAt_adicCompletion_of_forall_not_isMaximal (solution)

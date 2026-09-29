-- Prove2me | solution 1 for Algebra.exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/59234d56-82f3-5b16-99be-b7105995ce40

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential

set_option autoImplicit false

open Topology Polynomial TensorProduct

namespace EtaleCoordC1a

variable {S : Type} [CommRing S]

theorem rankAtStalk_eq_one [IsDomain S] {M : Type} [AddCommGroup M] [Module S M] [Module.FinitePresentation S M]
    [Module.Flat S M] (hrank : Module.rank S M = 1) (p : PrimeSpectrum S) : Module.rankAtStalk M p = 1 := by
  rw [(Module.isLocallyConstant_rankAtStalk (R := S) (M := M)).apply_eq_of_preconnectedSpace p ⟨⊥, Ideal.isPrime_bot⟩]
  have hle : (⊥ : Ideal S).primeCompl ≤ nonZeroDivisors S := by
    intro x hx
    exact mem_nonZeroDivisors_of_ne_zero (fun h0 => hx (h0 ▸ (Submodule.zero_mem ⊥ : (0 : S) ∈ (⊥ : Ideal S))))
  have hr : Module.rank (Localization.AtPrime (⊥ : Ideal S)) (LocalizedModule (⊥ : Ideal S).primeCompl M) = 1 := by
    rw [IsLocalization.rank_eq (S := Localization.AtPrime (⊥ : Ideal S)) (p := (⊥ : Ideal S).primeCompl) (hp := hle),
      IsLocalizedModule.rank_eq (p := (⊥ : Ideal S).primeCompl) (f := LocalizedModule.mkLinearMap (⊥ : Ideal S).primeCompl M)
        (hp := hle), hrank]
  show Module.finrank (Localization.AtPrime (⊥ : Ideal S)) (LocalizedModule (⊥ : Ideal S).primeCompl M) = 1
  exact Module.finrank_eq_of_rank_eq (by rw [hr, Nat.cast_one])

theorem mem_smul_top_of_mk_mem {M : Type} [AddCommGroup M] [Module S M] (𝔪 : Ideal S) [𝔪.IsMaximal] (x : M)
    (h : LocalizedModule.mk x (1 : 𝔪.primeCompl) ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) • (⊤ : Submodule (Localization.AtPrime 𝔪)
        (LocalizedModule 𝔪.primeCompl M))) :
    x ∈ 𝔪 • (⊤ : Submodule S M) := by
  have key : (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) • (⊤ : Submodule (Localization.AtPrime 𝔪)
      (LocalizedModule 𝔪.primeCompl M)) = (𝔪 • (⊤ : Submodule S M)).localized' (Localization.AtPrime 𝔪) 𝔪.primeCompl
        (LocalizedModule.mkLinearMap 𝔪.primeCompl M) := by
    rw [Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top, Localization.AtPrime.map_eq_maximalIdeal]
  rw [key, Submodule.mem_localized', IsLocalizedModule.mk_eq_mk'] at h
  obtain ⟨m, hm, s, hms⟩ := h
  rw [IsLocalizedModule.mk'_eq_mk'_iff] at hms
  obtain ⟨c, hc⟩ := hms
  have hcx : ((c : S) * (s : S)) • x = (c : S) • m := by
    have := hc
    simp only [one_smul, Submonoid.smul_def, smul_smul] at this
    exact this
  have hnot : (c : S) * (s : S) ∉ 𝔪 := ‹𝔪.IsMaximal›.isPrime.mul_notMem c.2 s.2
  obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv ‹𝔪.IsMaximal› hnot
  have hx : x = y • (((c : S) * (s : S)) • x) + i • x := by
    rw [smul_smul, ← add_smul, hyi, one_smul]
  rw [hx, hcx]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hm))
    (Submodule.smul_mem_smul hi Submodule.mem_top)

attribute [local instance] Module.free_of_flat_of_isLocalRing in
theorem bijective_smul_mk {M : Type} [AddCommGroup M] [Module S M] [Module.Finite S M] [Module.Flat S M]
    (𝔪 : Ideal S) [𝔪.IsMaximal] (h1 : Module.rankAtStalk M ⟨𝔪, inferInstance⟩ = 1)
    (x : M) (hx : x ∉ 𝔪 • (⊤ : Submodule S M)) :
    Function.Bijective (fun s : Localization.AtPrime 𝔪 => s • LocalizedModule.mk x (1 : 𝔪.primeCompl)) := by
  set ω : LocalizedModule 𝔪.primeCompl M := LocalizedModule.mk x (1 : 𝔪.primeCompl) with hω
  have h1' : Module.finrank (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) = 1 := h1
  let b := Module.finBasisOfFinrankEq (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) h1'
  set u : Localization.AtPrime 𝔪 := b.repr ω 0 with hu
  have hωu : ω = u • b 0 := by
    have := b.sum_repr ω
    rw [Fin.sum_univ_one] at this
    exact this.symm
  have hunit : IsUnit u := by
    by_contra hnu
    apply hx
    apply mem_smul_top_of_mk_mem 𝔪 x
    rw [← hω, hωu]
    exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal u).2 (mem_nonunits_iff.2 hnu)) Submodule.mem_top
  have hrepr : ∀ s : Localization.AtPrime 𝔪, b.repr (s • ω) 0 = s * u := by
    intro s
    rw [hωu, smul_smul, map_smul, b.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_eq_same]
  constructor
  · intro s s' hss'
    have := congrArg (fun z => b.repr z 0) hss'
    simp only [hrepr] at this
    exact hunit.mul_left_injective this
  · intro y
    refine ⟨b.repr y 0 * ↑hunit.unit⁻¹, ?_⟩
    show (b.repr y 0 * ↑hunit.unit⁻¹) • ω = y
    rw [hωu, smul_smul, mul_assoc, IsUnit.val_inv_mul, mul_one]
    have := b.sum_repr y
    rw [Fin.sum_univ_one] at this
    exact this

theorem exists_eq_tmul_D_X [Algebra ℂ[X] S] (z : S ⊗[ℂ[X]] Ω[ℂ[X]⁄ℂ]) :
    ∃ a : S, z = a ⊗ₜ[ℂ[X]] KaehlerDifferential.D ℂ ℂ[X] X := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [TensorProduct.zero_tmul]⟩
  | tmul s ω =>
    refine ⟨KaehlerDifferential.polynomialEquiv ℂ ω • s, ?_⟩
    conv_lhs => rw [← (KaehlerDifferential.polynomialEquiv ℂ).symm_apply_apply ω, KaehlerDifferential.polynomialEquiv_symm]
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨a₁, rfl⟩ := h₁
    obtain ⟨a₂, rfl⟩ := h₂
    exact ⟨a₁ + a₂, by rw [TensorProduct.add_tmul]⟩

theorem D_algebraMap_eq_zero (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (r : R) :
    KaehlerDifferential.D R A (algebraMap R A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero]

theorem notMem_support_kaehlerDifferential [Algebra ℂ S] [Algebra ℂ[X] S] [IsScalarTower ℂ ℂ[X] S]
    (t : S) (hX : algebraMap ℂ[X] S X = t) (𝔪 : Ideal S) [𝔪.IsMaximal]
    (hψ : Function.Surjective (fun s : Localization.AtPrime 𝔪 =>
      s • LocalizedModule.mk (KaehlerDifferential.D ℂ S t) (1 : 𝔪.primeCompl))) :
    (⟨𝔪, Ideal.IsMaximal.isPrime inferInstance⟩ : PrimeSpectrum S) ∉ Module.support S (Ω[S⁄ℂ[X]]) := by
  rw [Module.notMem_support_iff']
  intro m
  obtain ⟨ω₁, rfl⟩ := KaehlerDifferential.map_surjective ℂ ℂ[X] S m
  obtain ⟨sₘ, hsₘ⟩ := hψ (LocalizedModule.mk ω₁ 1)
  obtain ⟨⟨a, c⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl sₘ
  have h2 := congrArg (fun z => algebraMap S (Localization.AtPrime 𝔪) (c : S) • z) hsₘ
  simp only at h2
  rw [smul_smul, IsLocalization.mk'_spec', algebraMap_smul, algebraMap_smul, LocalizedModule.smul'_mk,
    LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at h2
  obtain ⟨u, hu⟩ := h2
  have hu' : ((u : S) * (c : S)) • ω₁ = ((u : S) * a) • KaehlerDifferential.D ℂ S t := by
    have := hu
    simp only [one_smul, Submonoid.smul_def, smul_smul] at this
    exact this.symm
  refine ⟨(u : S) * (c : S), ‹𝔪.IsMaximal›.isPrime.mul_notMem u.2 c.2, ?_⟩
  rw [← LinearMap.map_smul, hu', LinearMap.map_smul, KaehlerDifferential.map_D, Algebra.algebraMap_self_apply, ← hX,
    D_algebraMap_eq_zero, smul_zero]

theorem notMem_support_h1Cotangent [Algebra ℂ S] [Algebra.FormallySmooth ℂ S] [Algebra ℂ[X] S] [IsScalarTower ℂ ℂ[X] S]
    (t : S) (hX : algebraMap ℂ[X] S X = t) (𝔪 : Ideal S) [𝔪.IsMaximal]
    (hψ : Function.Injective (fun s : Localization.AtPrime 𝔪 =>
      s • LocalizedModule.mk (KaehlerDifferential.D ℂ S t) (1 : 𝔪.primeCompl))) :
    (⟨𝔪, Ideal.IsMaximal.isPrime inferInstance⟩ : PrimeSpectrum S) ∉ Module.support S (Algebra.H1Cotangent ℂ[X] S) := by
  rw [Module.notMem_support_iff']
  intro h
  have hinj : Function.Injective (Algebra.H1Cotangent.δ ℂ ℂ[X] S) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ (R := ℂ) (S := ℂ[X]) (T := S) z).1 hz
    rw [Subsingleton.elim w 0, LinearMap.map_zero]
  have hδ0 : KaehlerDifferential.mapBaseChange ℂ ℂ[X] S (Algebra.H1Cotangent.δ ℂ ℂ[X] S h) = 0 :=
    (Algebra.H1Cotangent.exact_δ_mapBaseChange (R := ℂ) (S := ℂ[X]) (T := S) _).2 ⟨h, rfl⟩
  obtain ⟨a, ha⟩ := exists_eq_tmul_D_X (Algebra.H1Cotangent.δ ℂ ℂ[X] S h)
  rw [ha, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, hX] at hδ0

  have h0 : algebraMap S (Localization.AtPrime 𝔪) a = 0 := by
    apply hψ
    show algebraMap S (Localization.AtPrime 𝔪) a • LocalizedModule.mk (KaehlerDifferential.D ℂ S t) (1 : 𝔪.primeCompl) =
      (0 : Localization.AtPrime 𝔪) • LocalizedModule.mk (KaehlerDifferential.D ℂ S t) (1 : 𝔪.primeCompl)
    rw [algebraMap_smul, LocalizedModule.smul'_mk, hδ0, LocalizedModule.zero_mk, zero_smul]
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff 𝔪.primeCompl (Localization.AtPrime 𝔪) a).1 h0
  refine ⟨c, c.2, hinj ?_⟩
  rw [LinearMap.map_smul, map_zero, ha, TensorProduct.smul_tmul', smul_eq_mul, hc, TensorProduct.zero_tmul]

end EtaleCoordC1a

open EtaleCoordC1a in
theorem solution
    (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (hsm : Algebra.Smooth ℂ S)
    (hrank : Module.rank S (KaehlerDifferential ℂ S) = 1)
    (σ₀ : S →ₐ[ℂ] ℂ) (t : S)
    (hdt : KaehlerDifferential.D ℂ S t ∉ (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S))) :
    ∃ (g : S), σ₀ g ≠ 0 ∧
      letI : Algebra (Polynomial ℂ) (Localization.Away g) :=
        ((algebraMap S (Localization.Away g)).comp (Polynomial.aeval t).toRingHom).toAlgebra
      Algebra.IsStandardEtale (Polynomial ℂ) (Localization.Away g) := by
  classical
  haveI := hsm
  letI algX : Algebra ℂ[X] S := (Polynomial.aeval t).toRingHom.toAlgebra
  have halg : ∀ p : ℂ[X], algebraMap ℂ[X] S p = Polynomial.aeval t p := fun _ => rfl
  haveI : IsScalarTower ℂ ℂ[X] S := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [halg, Polynomial.algebraMap_eq, Polynomial.aeval_C])
  have hX : algebraMap ℂ[X] S X = t := by rw [halg, Polynomial.aeval_X]
  haveI : Algebra.FiniteType ℂ[X] S := Algebra.FiniteType.of_restrictScalars_finiteType ℂ ℂ[X] S
  haveI : Algebra.FinitePresentation ℂ[X] S := (Algebra.FinitePresentation.of_finiteType (R := ℂ[X]) (A := S)).mp ‹_›

  set 𝔪 : Ideal S := RingHom.ker σ₀.toRingHom with h𝔪
  haveI h𝔪max : 𝔪.IsMaximal := by
    rw [h𝔪]; exact RingHom.ker_isMaximal_of_surjective σ₀.toRingHom (fun c => ⟨algebraMap ℂ S c, σ₀.commutes c⟩)

  have h1 : Module.rankAtStalk (Ω[S⁄ℂ]) ⟨𝔪, inferInstance⟩ = 1 := rankAtStalk_eq_one hrank _
  have hψ := bijective_smul_mk 𝔪 h1 (KaehlerDifferential.D ℂ S t) (by rw [h𝔪]; exact hdt)
  have hEt : Algebra.IsEtaleAt ℂ[X] 𝔪 := by
    have : (⟨𝔪, inferInstance⟩ : PrimeSpectrum S) ∈ Algebra.etaleLocus ℂ[X] S := by
      rw [Algebra.etaleLocus_eq_compl_support]
      exact ⟨notMem_support_kaehlerDifferential t hX 𝔪 hψ.2, notMem_support_h1Cotangent t hX 𝔪 hψ.1⟩
    exact Algebra.mem_etaleLocus_iff.1 this
  obtain ⟨g, hg𝔪, hSE⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := ℂ[X]) 𝔪
  refine ⟨g, fun h0 => hg𝔪 (by rw [h𝔪, RingHom.mem_ker]; exact h0), ?_⟩

  have hinst : (((algebraMap S (Localization.Away g)).comp (Polynomial.aeval t).toRingHom).toAlgebra :
      Algebra ℂ[X] (Localization.Away g)) = (inferInstance : Algebra ℂ[X] (Localization.Away g)) := by
    refine Algebra.algebra_ext _ _ (fun p => ?_)
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, IsScalarTower.algebraMap_apply ℂ[X] S (Localization.Away g),
      halg]
    rfl
  rw [hinst]
  exact hSE

end S_Algebra_exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential
end P2MW
export P2MW.S_Algebra_exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential (solution)

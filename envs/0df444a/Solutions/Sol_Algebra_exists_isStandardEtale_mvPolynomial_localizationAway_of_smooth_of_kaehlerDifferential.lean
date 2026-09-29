-- Prove2me | solution 1 for Algebra.exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5afddae5-c352-54d9-9b9d-85e077bbf11c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential

set_option autoImplicit false

open Topology TensorProduct

namespace EtaleCoordK1a

variable {S : Type} [CommRing S]

theorem rankAtStalk_eq [IsDomain S] {M : Type} [AddCommGroup M] [Module S M] [Module.FinitePresentation S M]
    [Module.Flat S M] {n : ℕ} (hrank : Module.rank S M = n) (p : PrimeSpectrum S) : Module.rankAtStalk M p = n := by
  rw [(Module.isLocallyConstant_rankAtStalk (R := S) (M := M)).apply_eq_of_preconnectedSpace p ⟨⊥, Ideal.isPrime_bot⟩]
  have hle : (⊥ : Ideal S).primeCompl ≤ nonZeroDivisors S := by
    intro x hx
    exact mem_nonZeroDivisors_of_ne_zero (fun h0 => hx (h0 ▸ (Submodule.zero_mem ⊥ : (0 : S) ∈ (⊥ : Ideal S))))
  have hr : Module.rank (Localization.AtPrime (⊥ : Ideal S)) (LocalizedModule (⊥ : Ideal S).primeCompl M) = n := by
    rw [IsLocalization.rank_eq (S := Localization.AtPrime (⊥ : Ideal S)) (p := (⊥ : Ideal S).primeCompl) (hp := hle),
      IsLocalizedModule.rank_eq (p := (⊥ : Ideal S).primeCompl) (f := LocalizedModule.mkLinearMap (⊥ : Ideal S).primeCompl M)
        (hp := hle), hrank]
  show Module.finrank (Localization.AtPrime (⊥ : Ideal S)) (LocalizedModule (⊥ : Ideal S).primeCompl M) = n
  exact Module.finrank_eq_of_rank_eq (by rw [hr])

theorem exists_smul_mem_of_mk_mem {M : Type} [AddCommGroup M] [Module S M] (𝔭 : Ideal S) [𝔭.IsPrime]
    (N : Submodule S M) (x : M)
    (h : LocalizedModule.mk x (1 : 𝔭.primeCompl) ∈
      N.localized' (Localization.AtPrime 𝔭) 𝔭.primeCompl (LocalizedModule.mkLinearMap 𝔭.primeCompl M)) :
    ∃ r : S, r ∉ 𝔭 ∧ r • x ∈ N := by
  rw [Submodule.mem_localized', IsLocalizedModule.mk_eq_mk'] at h
  obtain ⟨m, hm, s, hms⟩ := h
  rw [IsLocalizedModule.mk'_eq_mk'_iff] at hms
  obtain ⟨c, hc⟩ := hms
  have hcx : ((c : S) * (s : S)) • x = (c : S) • m := by
    have := hc
    simp only [one_smul, Submonoid.smul_def, smul_smul] at this
    exact this
  exact ⟨(c : S) * (s : S), ‹𝔭.IsPrime›.mul_notMem c.2 s.2, by rw [hcx]; exact N.smul_mem _ hm⟩

theorem localized'_sup {M N : Type} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    (p : Submonoid S) (T : Type) [CommRing T] [Algebra S T] [IsLocalization p T] [Module T N]
    [IsScalarTower S T N] (f : M →ₗ[S] N) [IsLocalizedModule p f] (A B : Submodule S M) :
    (A ⊔ B).localized' T p f = A.localized' T p f ⊔ B.localized' T p f :=
  (Submodule.localized'gi T p f).gc.l_sup

attribute [local instance] Module.free_of_flat_of_isLocalRing in

theorem bijective_linearCombination {M : Type} [AddCommGroup M] [Module S M] [Module.Finite S M] [Module.Flat S M]
    (𝔪 : Ideal S) [𝔪.IsMaximal] {n : ℕ} (hn : Module.rankAtStalk M ⟨𝔪, inferInstance⟩ = n)
    (x : Fin n → M) (hx : 𝔪 • (⊤ : Submodule S M) ⊔ Submodule.span S (Set.range x) = ⊤) :
    Function.Bijective (Fintype.linearCombination (Localization.AtPrime 𝔪)
      (fun i => LocalizedModule.mk (x i) (1 : 𝔪.primeCompl))) := by
  set ω : Fin n → LocalizedModule 𝔪.primeCompl M := fun i => LocalizedModule.mk (x i) (1 : 𝔪.primeCompl) with hω
  set ψ := Fintype.linearCombination (Localization.AtPrime 𝔪) ω with hψ
  have hn' : Module.finrank (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) = n := hn

  have hloc := congrArg (Submodule.localized' (Localization.AtPrime 𝔪) 𝔪.primeCompl
    (LocalizedModule.mkLinearMap 𝔪.primeCompl M)) hx
  rw [localized'_sup, Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top,
    Localization.AtPrime.map_eq_maximalIdeal, Submodule.localized'_span, ← Set.range_comp] at hloc
  have hrange : (LocalizedModule.mkLinearMap 𝔪.primeCompl M) ∘ x = ω := by
    funext i; rfl
  rw [hrange] at hloc
  have hspan : Submodule.span (Localization.AtPrime 𝔪) (Set.range ω) = ⊤ := by
    refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot (N' := ⊤) Module.Finite.fg_top
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_)
    rw [sup_comm, hloc]
  have hsurj : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top, hψ, Fintype.range_linearCombination, hspan]

  let b := Module.finBasisOfFinrankEq (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) hn'
  have hcomp : Function.Surjective (b.equivFun.toLinearMap.comp ψ) :=
    b.equivFun.surjective.comp hsurj
  have hinj : Function.Injective (b.equivFun.toLinearMap.comp ψ) :=
    OrzechProperty.injective_of_surjective_endomorphism _ hcomp
  have hinj' : Function.Injective (⇑b.equivFun ∘ ⇑ψ) := by
    rw [LinearMap.coe_comp, LinearEquiv.coe_coe] at hinj
    exact hinj
  exact ⟨Function.Injective.of_comp hinj', hsurj⟩

theorem D_algebraMap_eq_zero (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (r : R) :
    KaehlerDifferential.D R A (algebraMap R A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero]

theorem notMem_support_kaehlerDifferential {R : Type} [CommRing R] [Algebra ℂ R] [Algebra ℂ S] [Algebra R S]
    [IsScalarTower ℂ R S] {n : ℕ} (t : Fin n → S) (ht : ∀ i, ∃ r : R, algebraMap R S r = t i)
    (𝔪 : Ideal S) [𝔪.IsMaximal]
    (hspan : Submodule.span (Localization.AtPrime 𝔪)
      (Set.range fun i => LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl)) = ⊤) :
    (⟨𝔪, Ideal.IsMaximal.isPrime inferInstance⟩ : PrimeSpectrum S) ∉ Module.support S (Ω[S⁄R]) := by
  rw [Module.notMem_support_iff']
  intro m
  obtain ⟨ω₁, rfl⟩ := KaehlerDifferential.map_surjective ℂ R S m
  have hmem : LocalizedModule.mk ω₁ (1 : 𝔪.primeCompl) ∈
      (Submodule.span S (Set.range fun i => KaehlerDifferential.D ℂ S (t i))).localized' (Localization.AtPrime 𝔪)
        𝔪.primeCompl (LocalizedModule.mkLinearMap 𝔪.primeCompl (Ω[S⁄ℂ])) := by
    rw [Submodule.localized'_span, ← Set.range_comp]
    have : (LocalizedModule.mkLinearMap 𝔪.primeCompl (Ω[S⁄ℂ])) ∘ (fun i => KaehlerDifferential.D ℂ S (t i)) =
        fun i => LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl) := by
      funext i; rfl
    rw [this, hspan]
    trivial
  obtain ⟨r, hr, hrω⟩ := exists_smul_mem_of_mk_mem 𝔪 _ ω₁ hmem
  refine ⟨r, hr, ?_⟩
  rw [← LinearMap.map_smul]
  have hle : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℂ S (t i)) ≤
      LinearMap.ker (KaehlerDifferential.map ℂ R S S) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨ri, hri⟩ := ht i
    show KaehlerDifferential.D ℂ S (t i) ∈ LinearMap.ker (KaehlerDifferential.map ℂ R S S)
    rw [LinearMap.mem_ker, KaehlerDifferential.map_D, Algebra.algebraMap_self_apply, ← hri, D_algebraMap_eq_zero]
  exact hle hrω

theorem notMem_support_h1Cotangent [Algebra ℂ S] [Algebra.FormallySmooth ℂ S] {n : ℕ}
    [Algebra (MvPolynomial (Fin n) ℂ) S] [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) S]
    (t : Fin n → S) (hX : ∀ i, algebraMap (MvPolynomial (Fin n) ℂ) S (MvPolynomial.X i) = t i)
    (𝔪 : Ideal S) [𝔪.IsMaximal]
    (hψ : Function.Injective (Fintype.linearCombination (Localization.AtPrime 𝔪)
      (fun i => LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl)))) :
    (⟨𝔪, Ideal.IsMaximal.isPrime inferInstance⟩ : PrimeSpectrum S) ∉
      Module.support S (Algebra.H1Cotangent (MvPolynomial (Fin n) ℂ) S) := by
  classical
  set R := MvPolynomial (Fin n) ℂ with hR
  rw [Module.notMem_support_iff']
  intro h
  have hinj : Function.Injective (Algebra.H1Cotangent.δ ℂ R S) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ (R := ℂ) (S := R) (T := S) z).1 hz
    rw [Subsingleton.elim w 0, LinearMap.map_zero]
  have hδ0 : KaehlerDifferential.mapBaseChange ℂ R S (Algebra.H1Cotangent.δ ℂ R S h) = 0 :=
    (Algebra.H1Cotangent.exact_δ_mapBaseChange (R := ℂ) (S := R) (T := S) _).2 ⟨h, rfl⟩

  let B : Module.Basis (Fin n) S (S ⊗[R] Ω[R⁄ℂ]) :=
    Algebra.TensorProduct.basis S (KaehlerDifferential.mvPolynomialBasis ℂ (Fin n))
  have hB : ∀ i, B i = (1 : S) ⊗ₜ[R] KaehlerDifferential.D ℂ R (MvPolynomial.X i) := by
    intro i
    rw [show B i = Algebra.TensorProduct.basis S (KaehlerDifferential.mvPolynomialBasis ℂ (Fin n)) i from rfl,
      Algebra.TensorProduct.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply]
  set a : Fin n → S := fun i => B.repr (Algebra.H1Cotangent.δ ℂ R S h) i with ha
  have hsum : Algebra.H1Cotangent.δ ℂ R S h = ∑ i, a i • B i := (B.sum_repr _).symm
  have hmap : ∀ i, KaehlerDifferential.mapBaseChange ℂ R S (B i) = KaehlerDifferential.D ℂ S (t i) := by
    intro i
    rw [hB, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, hX, one_smul]
  have hzero : ∑ i, a i • KaehlerDifferential.D ℂ S (t i) = 0 := by
    have := hδ0
    rw [hsum, map_sum] at this
    simp only [map_smul, hmap] at this
    exact this

  have hloc : Fintype.linearCombination (Localization.AtPrime 𝔪)
      (fun i => LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl))
      (fun i => algebraMap S (Localization.AtPrime 𝔪) (a i)) = 0 := by
    rw [Fintype.linearCombination_apply]
    have : ∀ i, algebraMap S (Localization.AtPrime 𝔪) (a i) •
        LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl) =
        LocalizedModule.mkLinearMap 𝔪.primeCompl (Ω[S⁄ℂ]) (a i • KaehlerDifferential.D ℂ S (t i)) := by
      intro i
      rw [algebraMap_smul, LinearMap.map_smul]
      rfl
    simp only [this, ← map_sum, hzero, map_zero]
  have hai : ∀ i, algebraMap S (Localization.AtPrime 𝔪) (a i) = 0 := by
    intro i
    have := hψ (hloc.trans (map_zero _).symm)
    exact congrFun this i
  choose c hc using fun i => (IsLocalization.map_eq_zero_iff 𝔪.primeCompl (Localization.AtPrime 𝔪) (a i)).1 (hai i)

  set C : 𝔪.primeCompl := ∏ i, c i with hC
  have hCa : ∀ i, (C : S) * a i = 0 := by
    intro i
    rw [hC, Submonoid.coe_finset_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc, hc i, mul_zero]
  refine ⟨C, C.2, hinj ?_⟩
  rw [LinearMap.map_smul, map_zero, hsum, Finset.smul_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [smul_smul, hCa i, zero_smul]

end EtaleCoordK1a

open EtaleCoordK1a in
theorem solution
    (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (hsm : Algebra.Smooth ℂ S)
    {n : ℕ} (hrank : Module.rank S (KaehlerDifferential ℂ S) = n)
    (σ₀ : S →ₐ[ℂ] ℂ) (t : Fin n → S)
    (hdt : (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S)) ⊔
        Submodule.span S (Set.range fun i : Fin n => KaehlerDifferential.D ℂ S (t i)) = ⊤) :
    ∃ g : S, σ₀ g ≠ 0 ∧
      letI : Algebra (MvPolynomial (Fin n) ℂ) (Localization.Away g) :=
        ((algebraMap S (Localization.Away g)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
      Algebra.IsStandardEtale (MvPolynomial (Fin n) ℂ) (Localization.Away g) := by
  classical
  haveI := hsm
  letI algX : Algebra (MvPolynomial (Fin n) ℂ) S := (MvPolynomial.aeval t).toRingHom.toAlgebra
  have halg : ∀ p : MvPolynomial (Fin n) ℂ, algebraMap (MvPolynomial (Fin n) ℂ) S p = MvPolynomial.aeval t p :=
    fun _ => rfl
  haveI : IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) S := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [halg, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C])
  have hX : ∀ i, algebraMap (MvPolynomial (Fin n) ℂ) S (MvPolynomial.X i) = t i := fun i => by
    rw [halg, MvPolynomial.aeval_X]
  haveI : Algebra.FiniteType (MvPolynomial (Fin n) ℂ) S :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (MvPolynomial (Fin n) ℂ) S
  haveI : Algebra.FinitePresentation (MvPolynomial (Fin n) ℂ) S :=
    (Algebra.FinitePresentation.of_finiteType (R := MvPolynomial (Fin n) ℂ) (A := S)).mp ‹_›

  set 𝔪 : Ideal S := RingHom.ker σ₀.toRingHom with h𝔪
  haveI h𝔪max : 𝔪.IsMaximal := by
    rw [h𝔪]; exact RingHom.ker_isMaximal_of_surjective σ₀.toRingHom (fun c => ⟨algebraMap ℂ S c, σ₀.commutes c⟩)

  have hn : Module.rankAtStalk (Ω[S⁄ℂ]) ⟨𝔪, inferInstance⟩ = n := rankAtStalk_eq hrank _
  have hψ := bijective_linearCombination 𝔪 hn (fun i => KaehlerDifferential.D ℂ S (t i)) (by rw [h𝔪]; exact hdt)
  have hspan : Submodule.span (Localization.AtPrime 𝔪)
      (Set.range fun i => LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl)) = ⊤ := by
    rw [← Fintype.range_linearCombination, LinearMap.range_eq_top]
    exact hψ.2
  have hEt : Algebra.IsEtaleAt (MvPolynomial (Fin n) ℂ) 𝔪 := by
    have : (⟨𝔪, inferInstance⟩ : PrimeSpectrum S) ∈ Algebra.etaleLocus (MvPolynomial (Fin n) ℂ) S := by
      rw [Algebra.etaleLocus_eq_compl_support]
      exact ⟨notMem_support_kaehlerDifferential t (fun i => ⟨MvPolynomial.X i, hX i⟩) 𝔪 hspan,
        notMem_support_h1Cotangent t hX 𝔪 hψ.1⟩
    exact Algebra.mem_etaleLocus_iff.1 this
  obtain ⟨g, hg𝔪, hSE⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := MvPolynomial (Fin n) ℂ) 𝔪
  refine ⟨g, fun h0 => hg𝔪 (by rw [h𝔪, RingHom.mem_ker]; exact h0), ?_⟩

  have hinst : (((algebraMap S (Localization.Away g)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra :
      Algebra (MvPolynomial (Fin n) ℂ) (Localization.Away g)) =
      (inferInstance : Algebra (MvPolynomial (Fin n) ℂ) (Localization.Away g)) := by
    refine Algebra.algebra_ext _ _ (fun p => ?_)
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) ℂ) S (Localization.Away g), halg]
    rfl
  rw [hinst]
  exact hSE

end S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential
end P2MW
export P2MW.S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential (solution)

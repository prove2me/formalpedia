-- Prove2me | solution 1 for AlgebraicCurve.NodeAnnulusEngine.finsum_finrank_quotient_eq_length_of_comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/29a6b51b-cb2a-5a52-9d3a-d110496d1b24

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_isReduced_quotient_map_of_ne_bot_of_not_mem
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_IsLocalRing_eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two
import Theorems.Thm_ModularCurve_UVCrossingModel_ringKrullDim_le_two
import Theorems.Thm_ModularCurve_UVCrossingModel_free_and_finite_quotient_of_ne_bot_of_const_notMem
import Theorems.Thm_ModularCurve_UVCrossingModel_isAdicComplete_maximalIdeal
import Theorems.Thm_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_sub_const_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finsum_finrank_quotient_eq_length_of_comap_eq

set_option autoImplicit false

namespace AdicCompletion
p2m_export "AdicCompletion" "map eval mk ofAlgEquiv eval_of of map_of module mk_surjective map_zero of_injective ext pow_smul_top_eq_ker_eval pi sum mkₐ"
p2m_open "AdicCompletion"

open Submodule

variable {N : Type*} [CommRing N] (I : Ideal N)

theorem algebraMap_apply_eq_of (x : N) : algebraMap N (AdicCompletion I N) x = of I N x := rfl

theorem map_le_ker_map_mkQ (𝔞 : Ideal N) :
    𝔞.map (algebraMap N (AdicCompletion I N)) ≤
      LinearMap.ker (map I (𝔞.mkQ : N →ₗ[N] N ⧸ 𝔞)) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap]
  refine LinearMap.mem_ker.mpr ?_
  rw [algebraMap_apply_eq_of, map_of, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero 𝔞).mpr ha,
    LinearMap.map_zero]

theorem comap_map_eq_of_isHausdorff (𝔞 : Ideal N) [IsHausdorff I (N ⧸ 𝔞)] :
    (𝔞.map (algebraMap N (AdicCompletion I N))).comap (algebraMap N (AdicCompletion I N)) = 𝔞 := by
  refine le_antisymm ?_ Ideal.le_comap_map
  intro x hx
  rw [Ideal.mem_comap] at hx
  have h0 : map I (𝔞.mkQ : N →ₗ[N] N ⧸ 𝔞) (of I N x) = 0 := map_le_ker_map_mkQ I 𝔞 hx
  rw [map_of] at h0
  have h1 : (𝔞.mkQ : N →ₗ[N] N ⧸ 𝔞) x = 0 := of_injective I (N ⧸ 𝔞) (by rw [h0, LinearMap.map_zero])
  rw [Submodule.mkQ_apply] at h1
  exact (Submodule.Quotient.mk_eq_zero 𝔞).mp h1

theorem isHausdorff_of_pow_smul_top_eq_bot {M : Type*} [AddCommGroup M] [Module N M] {k : ℕ}
    (hk : (I ^ k • ⊤ : Submodule N M) = ⊥) : IsHausdorff I M := by
  refine ⟨fun x hx => ?_⟩
  have := hx k
  rw [SModEq.zero, hk, Submodule.mem_bot] at this
  exact this

theorem isHausdorff_quotient_of_pow_le (𝔞 : Ideal N) {k : ℕ} (hk : I ^ k ≤ 𝔞) :
    IsHausdorff I (N ⧸ 𝔞) := by
  refine isHausdorff_of_pow_smul_top_eq_bot I (k := k) ?_
  rw [eq_bot_iff]
  refine Submodule.smul_le.mpr fun r hr m _ => ?_
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective 𝔞 m
  rw [Submodule.mem_bot, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Ideal.mul_mem_right _ _ (hk hr)

theorem quotientMap_bijective_of_pow_le (hI : I.FG) (𝔞 : Ideal N) {k : ℕ} (hk : I ^ k ≤ 𝔞) :
    Function.Bijective (Ideal.quotientMap (𝔞.map (algebraMap N (AdicCompletion I N)))
      (algebraMap N (AdicCompletion I N)) Ideal.le_comap_map) := by
  haveI := isHausdorff_quotient_of_pow_le I 𝔞 hk
  refine ⟨Ideal.quotientMap_injective' (le_of_eq (comap_map_eq_of_isHausdorff I 𝔞)), ?_⟩
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective _ (eval I N k y)
  refine ⟨Ideal.Quotient.mk 𝔞 n, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, algebraMap_apply_eq_of]
  have hker : of I N n - y ∈ LinearMap.ker (eval I N k) := by
    rw [LinearMap.mem_ker, LinearMap.map_sub, eval_of, sub_eq_zero]
    exact hn
  rw [← pow_smul_top_eq_ker_eval hI, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] at hker
  exact Ideal.map_mono hk hker

noncomputable def quotientEquivOfPowLe (hI : I.FG) (𝔞 : Ideal N) {k : ℕ} (hk : I ^ k ≤ 𝔞) :
    (N ⧸ 𝔞) ≃+* (AdicCompletion I N ⧸ 𝔞.map (algebraMap N (AdicCompletion I N))) :=
  RingEquiv.ofBijective _ (quotientMap_bijective_of_pow_le I hI 𝔞 hk)

theorem quotientEquivOfPowLe_mk (hI : I.FG) (𝔞 : Ideal N) {k : ℕ} (hk : I ^ k ≤ 𝔞) (x : N) :
    quotientEquivOfPowLe I hI 𝔞 hk (Ideal.Quotient.mk 𝔞 x) =
      Ideal.Quotient.mk _ (algebraMap N (AdicCompletion I N) x) := rfl

end AdicCompletion

section LengthTransfer

p2m_open "IsLocalRing P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finsum_finrank_quotient_eq_length_of_comap_eq.IsLocalRing"

variable {A R : Type*} [CommRing A] [CommRing R] [IsLocalRing R] [Algebra A R]

namespace IsSimpleModule p2m_export "IsSimpleModule" "mk nontrivial toSpanSingleton_surjective annihilator_isMaximal" end IsSimpleModule
p2m_open_scoped "IsSimpleModule" in

theorem IsSimpleModule.of_surjective_residue_comp_algebraMap
    (h : Function.Surjective ((residue R).comp (algebraMap A R)))
    (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M] [IsSimpleModule R M] :
    IsSimpleModule A M := by
  have hann : Module.annihilator R M = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (IsSimpleModule.annihilator_isMaximal (R := R) (M := M))
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨IsSimpleModule.nontrivial R M, fun x hx z => ?_⟩
  obtain ⟨r, rfl⟩ := IsSimpleModule.toSpanSingleton_surjective R hx z
  obtain ⟨a, ha⟩ := h (residue R r)
  refine ⟨a, ?_⟩
  simp only [LinearMap.toSpanSingleton_apply]
  have hmem : r - algebraMap A R a ∈ maximalIdeal R := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    exact ha.symm
  rw [← hann, Module.mem_annihilator] at hmem
  have := hmem x
  rw [sub_smul, sub_eq_zero] at this
  rw [this, algebraMap_smul]

namespace Module p2m_export "Module" "length_eq_one length_eq_finrank Injective finrank_pi_fintype length_eq_zero mem_annihilator length_ne_top_iff finrank Free annihilator length_ne_top length_eq_add_of_exact mk Finite.of_injective free_of_finite_type_torsion_free' restrictScalars finrank_baseChange length_eq_of_surjective length" end Module
p2m_open_scoped "Module" in

theorem Module.length_restrictScalars_eq_of_surjective_residue_aux
    (h : Function.Surjective ((residue R).comp (algebraMap A R))) :
    ∀ (M : Type*) [AddCommGroup M] [Module R M], IsFiniteLength R M →
      ∀ [Module A M] [IsScalarTower A R M], Module.length A M = Module.length R M := by
  intro M _ _ hM
  induction hM with
  | of_subsingleton => intro _ _; rw [Module.length_eq_zero, Module.length_eq_zero]
  | @of_simple_quotient M _ _ N hsimp hN ih =>
    intro _ _
    have hR := Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.injective_subtype N)
      (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)
    have hA := Module.length_eq_add_of_exact (N.subtype.restrictScalars A) (N.mkQ.restrictScalars A)
      (Submodule.injective_subtype N) (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)
    haveI : IsSimpleModule A (M ⧸ N) := IsSimpleModule.of_surjective_residue_comp_algebraMap h (M ⧸ N)
    rw [hR, hA, ih, Module.length_eq_one A (M ⧸ N), Module.length_eq_one R (M ⧸ N)]

p2m_open_scoped "Module" in

theorem Module.length_restrictScalars_eq_of_surjective_residue
    (h : Function.Surjective ((residue R).comp (algebraMap A R)))
    {M : Type*} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    [Module A M] [IsScalarTower A R M] :
    Module.length A M = Module.length R M :=
  Module.length_restrictScalars_eq_of_surjective_residue_aux h M hM

end LengthTransfer

section RankSandwich

variable {W : Type*} [CommRing W] [IsNoetherianRing W] [Nontrivial W]

p2m_open_scoped "Module" in

theorem Module.finrank_eq_of_injective_of_smul_mem_range
    {T P : Type*} [AddCommGroup T] [Module W T] [AddCommGroup P] [Module W P] [Module.Finite W P]
    (φ : T →ₗ[W] P) (hφ : Function.Injective φ) (w : W) (hw : IsSMulRegular P w)
    (hP : ∀ x : P, w • x ∈ LinearMap.range φ) :
    Module.finrank W T = Module.finrank W P := by
  haveI : Module.Finite W T := Module.Finite.of_injective φ hφ
  refine le_antisymm (LinearMap.finrank_le_finrank_of_injective hφ) ?_

  let e : T ≃ₗ[W] LinearMap.range φ := LinearEquiv.ofInjective φ hφ
  let μ : P →ₗ[W] LinearMap.range φ := LinearMap.codRestrict (LinearMap.range φ) (w • LinearMap.id) (fun x => hP x)
  let ψ : P →ₗ[W] T := e.symm.toLinearMap.comp μ
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have : μ x = μ y := e.symm.injective hxy
    have : w • x = w • y := by
      have := congrArg Subtype.val this
      simpa [μ] using this
    exact hw this
  exact LinearMap.finrank_le_finrank_of_injective hψ

end RankSandwich

section RankSplit

variable {W : Type*} [CommRing W] [IsDomain W] [IsNoetherianRing W]
variable {R : Type*} [CommRing R] [Algebra W R]

p2m_open_scoped "Module" in

theorem Module.finrank_quotient_eq_sum_finrank_quotient_of_isRadical [DecidableEq (PrimeSpectrum R)]
    (J : Ideal R) (hJ : J.IsRadical) (𝓠 : Finset (PrimeSpectrum R))
    (h𝓠 : ∀ Q : PrimeSpectrum R, Q ∈ 𝓠 ↔ Q.asIdeal ∈ J.minimalPrimes)
    [hfree : ∀ Q : ↥𝓠, Module.Free W (R ⧸ Q.1.asIdeal)] [hfin : ∀ Q : ↥𝓠, Module.Finite W (R ⧸ Q.1.asIdeal)]
    (w : W) (hw : w ≠ 0)
    (hsep : ∀ Q₀ ∈ 𝓠, ∃ n : ℕ, algebraMap W R w ^ n ∈ (𝓠.erase Q₀).inf PrimeSpectrum.asIdeal ⊔ Q₀.asIdeal) :
    Module.Finite W (R ⧸ J) ∧ NoZeroSMulDivisors W (R ⧸ J) ∧
      Module.finrank W (R ⧸ J) = ∑ Q ∈ 𝓠, Module.finrank W (R ⧸ Q.asIdeal) := by
  classical
  have hJQ : ∀ Q ∈ 𝓠, J ≤ Q.asIdeal := fun Q hQ => ((h𝓠 Q).mp hQ).1.2

  let φ : (R ⧸ J) →ₗ[W] (∀ Q : ↥𝓠, R ⧸ Q.1.asIdeal) :=
    LinearMap.pi fun Q => (Ideal.Quotient.factorₐ W (hJQ Q.1 Q.2)).toLinearMap
  have hφmk : ∀ (x : R) (Q : ↥𝓠), φ (Ideal.Quotient.mk J x) Q = Ideal.Quotient.mk _ x := fun x Q => rfl
  have hφ : Function.Injective φ := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq, ← hJ.radical, ← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro I hI
    have hmem : (⟨I, hI.1.1⟩ : PrimeSpectrum R) ∈ 𝓠 := (h𝓠 _).mpr hI
    have := congrFun hxy ⟨_, hmem⟩
    rw [hφmk, hφmk, Ideal.Quotient.eq] at this
    exact this

  have hsep' : ∀ Q₀ : ↥𝓠, ∃ n : ℕ, ∀ m : ℕ, n ≤ m → ∃ a : R, (∀ Q : ↥𝓠, Q ≠ Q₀ → a ∈ Q.1.asIdeal) ∧
      algebraMap W R w ^ m - a ∈ Q₀.1.asIdeal := by
    intro Q₀
    obtain ⟨n, hn⟩ := hsep Q₀.1 Q₀.2
    refine ⟨n, fun m hm => ?_⟩
    have hmem : algebraMap W R w ^ m ∈ (𝓠.erase Q₀.1).inf PrimeSpectrum.asIdeal ⊔ Q₀.1.asIdeal := by
      rw [← Nat.add_sub_cancel' hm, pow_add]
      exact Ideal.mul_mem_right _ _ hn
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
    refine ⟨a, fun Q hne => ?_, ?_⟩
    · have : (𝓠.erase Q₀.1).inf PrimeSpectrum.asIdeal ≤ Q.1.asIdeal :=
        Finset.inf_le (Finset.mem_erase.mpr ⟨fun h => hne (Subtype.ext h), Q.2⟩)
      exact this ha
    · rw [← hab, add_sub_cancel_left]; exact hb
  choose nf hnf using hsep'
  obtain ⟨af, haf⟩ : ∃ af : ↥𝓠 → R, ∀ Q₀ : ↥𝓠, (∀ Q : ↥𝓠, Q ≠ Q₀ → af Q₀ ∈ Q.1.asIdeal) ∧
      algebraMap W R w ^ (Finset.univ.sup nf) - af Q₀ ∈ Q₀.1.asIdeal :=
    ⟨fun Q₀ => (hnf Q₀ _ (Finset.le_sup (Finset.mem_univ Q₀))).choose,
      fun Q₀ => (hnf Q₀ _ (Finset.le_sup (Finset.mem_univ Q₀))).choose_spec⟩
  set Nmax : ℕ := Finset.univ.sup nf

  have hP : ∀ x : (∀ Q : ↥𝓠, R ⧸ Q.1.asIdeal), (w ^ Nmax) • x ∈ LinearMap.range φ := by
    intro x
    have hx : x = ∑ Q₀ : ↥𝓠, Pi.single Q₀ (x Q₀) := (Finset.univ_sum_single x).symm
    rw [hx, Finset.smul_sum]
    refine Submodule.sum_mem _ fun Q₀ _ => ?_
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (x Q₀)
    refine ⟨Ideal.Quotient.mk J (af Q₀ * y), ?_⟩
    funext Q
    rw [hφmk, Pi.smul_apply]
    by_cases hQ : Q = Q₀
    · subst hQ
      rw [Pi.single_eq_same, ← hy, Algebra.smul_def, ← Ideal.Quotient.mk_comp_algebraMap, RingHom.comp_apply,
        ← map_mul, Ideal.Quotient.eq, ← sub_mul, map_pow]
      refine Ideal.mul_mem_right _ _ ?_
      rw [← neg_mem_iff, neg_sub]
      exact (haf Q).2
    · rw [Pi.single_eq_of_ne hQ, smul_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ ((haf Q₀).1 Q hQ)
  have hreg : IsSMulRegular (∀ Q : ↥𝓠, R ⧸ Q.1.asIdeal) (w ^ Nmax) :=
    fun a b hab => smul_right_injective (∀ Q : ↥𝓠, R ⧸ Q.1.asIdeal) (pow_ne_zero _ hw) hab
  refine ⟨Module.Finite.of_injective φ hφ, ?_, ?_⟩
  · refine ⟨fun {c x} h => ?_⟩
    by_contra hne
    push_neg at hne
    obtain ⟨hc, hx⟩ := hne
    apply hx
    apply hφ
    rw [LinearMap.map_zero]
    have : c • φ x = 0 := by rw [← LinearMap.map_smul, h, LinearMap.map_zero]
    exact (smul_eq_zero.mp this).resolve_left hc
  · rw [Module.finrank_eq_of_injective_of_smul_mem_range φ hφ (w ^ Nmax) hreg hP,
      Module.finrank_pi_fintype W, ← Finset.sum_coe_sort 𝓠]

end RankSplit

section FiniteLengthQuot

p2m_open "IsLocalRing P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finsum_finrank_quotient_eq_length_of_comap_eq.IsLocalRing"

namespace IsLocalRing p2m_export "IsLocalRing" "eq_maximalIdeal le_maximalIdeal maximalIdeal maximalIdeal.isMaximal mem_maximalIdeal residue_surjective of_injective residue eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two" end IsLocalRing
p2m_open_scoped "IsLocalRing" in
theorem IsLocalRing.isFiniteLength_quotient_of_pow_le {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (𝔟 : Ideal R) {k : ℕ} (hk : maximalIdeal R ^ k ≤ 𝔟) : IsFiniteLength R (R ⧸ 𝔟) := by
  rcases eq_or_ne 𝔟 ⊤ with h | h𝔟
  · subst h
    haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact .of_subsingleton
  haveI : Nontrivial (R ⧸ 𝔟) := Ideal.Quotient.nontrivial_iff.mpr h𝔟
  haveI : IsArtinianRing (R ⧸ 𝔟) := by
    rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
    refine ⟨inferInstance, Ring.KrullDimLE.mk₀ fun P hP => ?_⟩
    haveI := hP
    haveI : (P.comap (Ideal.Quotient.mk 𝔟)).IsPrime := Ideal.IsPrime.comap _
    have hPc : P.comap (Ideal.Quotient.mk 𝔟) = maximalIdeal R := by
      refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
      refine Ideal.IsPrime.le_of_pow_le (hk.trans ?_)
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact zero_mem P
    have hPeq : P = (maximalIdeal R).map (Ideal.Quotient.mk 𝔟) := by
      rw [← hPc, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    rw [hPeq]
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk 𝔟) Ideal.Quotient.mk_surjective
      (IsLocalRing.maximalIdeal.isMaximal R) with h | h
    · exact absurd (hPeq ▸ Ideal.IsPrime.ne_top hP) (by rw [h]; exact fun h => h rfl)
    · exact h
  rw [← Module.length_ne_top_iff, Module.length_eq_of_surjective (R := R ⧸ 𝔟) (S := R)
    (by exact Ideal.Quotient.mk_surjective)]
  exact Module.length_ne_top

end FiniteLengthQuot

section RankLength

p2m_open "IsLocalRing P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finsum_finrank_quotient_eq_length_of_comap_eq.IsLocalRing"
open scoped TensorProduct

p2m_open_scoped "Module" in
theorem Module.finrank_eq_length_quotient_maximalIdeal_smul_top {W : Type*} [CommRing W] [IsLocalRing W]
    (T : Type*) [AddCommGroup T] [Module W T] [Module.Free W T] [Module.Finite W T] :
    (Module.finrank W T : ℕ∞) = Module.length W (T ⧸ (maximalIdeal W • (⊤ : Submodule W T))) := by
  haveI := IsLocalRing.maximalIdeal.isMaximal W
  letI : Field (W ⧸ maximalIdeal W) := Ideal.Quotient.field _
  rw [← (TensorProduct.quotTensorEquivQuotSMul T (maximalIdeal W)).length_eq,
    Module.length_eq_of_surjective (S := W) (R := W ⧸ maximalIdeal W) (M := (W ⧸ maximalIdeal W) ⊗[W] T)
      Ideal.Quotient.mk_surjective,
    Module.length_eq_finrank, Module.finrank_baseChange]

p2m_open_scoped "Module" in
theorem Module.length_quotient_smul_top_quotient {W R : Type*} [CommRing W] [CommRing R] [Algebra W R]
    (I : Ideal W) (J : Ideal R) :
    Module.length W ((R ⧸ J) ⧸ (I • (⊤ : Submodule W (R ⧸ J)))) =
      Module.length W (R ⧸ (J ⊔ I.map (algebraMap W R))) := by
  have hsm : (I • (⊤ : Submodule W (R ⧸ J))) =
      ((I.map (algebraMap W R)).map (Ideal.Quotient.mkₐ W J)).restrictScalars W := by
    rw [Ideal.smul_top_eq_map, IsScalarTower.algebraMap_eq W R (R ⧸ J), ← Ideal.map_map, Ideal.Quotient.algebraMap_eq]
    rfl
  rw [hsm, (Submodule.Quotient.restrictScalarsEquiv W _).length_eq,
    (DoubleQuot.quotQuotEquivQuotSupₐ W J (I.map (algebraMap W R))).toLinearEquiv.length_eq]

end RankLength

section BCore

p2m_open "IsLocalRing P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finsum_finrank_quotient_eq_length_of_comap_eq.IsLocalRing ModularCurve ModularCurve.UVCrossingModel"
open scoped TensorProduct

universe u v

theorem finsum_finrank_quotient_eq_length_core
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    {N : Type v} [CommRing N] [IsDomain N] [IsLocalRing N] [IsNoetherianRing N]
    (ι : AdicCompletion (maximalIdeal N) N ≃+* UVCrossingModel W (π ^ E))
    (ϖN : N) (hϖN : ι (algebraMap N (AdicCompletion (maximalIdeal N) N) ϖN) = const (π ^ E) π)
    (𝔭 : Ideal N) [𝔭.IsPrime] (h𝔭0 : 𝔭 ≠ ⊥) (h𝔭ϖ : ϖN ∉ 𝔭)
    (hred : IsReduced (UVCrossingModel W (π ^ E) ⧸
      Ideal.map ((ι : AdicCompletion (maximalIdeal N) N →+* UVCrossingModel W (π ^ E)).comp
        (algebraMap N (AdicCompletion (maximalIdeal N) N))) 𝔭)) :
    ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
        (_ : Ideal.comap ((ι : AdicCompletion (maximalIdeal N) N →+* UVCrossingModel W (π ^ E)).comp
                (algebraMap N (AdicCompletion (maximalIdeal N) N))) Q.asIdeal = 𝔭),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) =
      Module.length N (N ⧸ (𝔭 ⊔ Ideal.span {ϖN})) := by
  classical

  haveI hRnoeth : IsNoetherianRing (UVCrossingModel W (π ^ E)) := UVCrossingModel.isNoetherianRing (π ^ E)
  obtain ⟨hRdom, hRloc, -⟩ := UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ E hE
  haveI := hRdom
  haveI := hRloc
  have hπu : ¬ IsUnit π := hπ.not_isUnit
  have hπEu : ¬ IsUnit (π ^ E) := fun h => hπu (isUnit_pow_iff (by omega) |>.mp h)
  have hmW : maximalIdeal W = Ideal.span {π} := hπ.maximalIdeal_eq
  set j : N →+* UVCrossingModel W (π ^ E) :=
    (ι : AdicCompletion (maximalIdeal N) N →+* UVCrossingModel W (π ^ E)).comp
      (algebraMap N (AdicCompletion (maximalIdeal N) N)) with hj
  have hjϖ : j ϖN = const (π ^ E) π := hϖN
  have hjinj : Function.Injective j :=
    ι.injective.comp (AdicCompletion.of_injective (maximalIdeal N) N)
  have hmNfg : (maximalIdeal N).FG := (isNoetherianRing_iff_ideal_fg N).mp inferInstance _

  have purity : ∀ 𝔞 : Ideal N, (𝔞.map j).comap j = 𝔞 := by
    intro 𝔞
    rw [hj, ← Ideal.map_map, ← Ideal.comap_comap,
      Ideal.comap_map_of_bijective (ι : AdicCompletion (maximalIdeal N) N →+* UVCrossingModel W (π ^ E)) ι.bijective]
    exact AdicCompletion.comap_map_eq_of_isHausdorff (maximalIdeal N) 𝔞

  have quotEquiv : ∀ (𝔞 : Ideal N) (k : ℕ), maximalIdeal N ^ k ≤ 𝔞 →
      ∃ e : (N ⧸ 𝔞) ≃+* (UVCrossingModel W (π ^ E) ⧸ 𝔞.map j), ∀ x : N, e (Ideal.Quotient.mk 𝔞 x) =
        Ideal.Quotient.mk _ (j x) := by
    intro 𝔞 k hk
    refine ⟨(AdicCompletion.quotientEquivOfPowLe (maximalIdeal N) hmNfg 𝔞 hk).trans
      (Ideal.quotientEquiv _ _ ι (by rw [hj, ← Ideal.map_map])), fun x => ?_⟩
    rw [RingEquiv.trans_apply, AdicCompletion.quotientEquivOfPowLe_mk, Ideal.quotientEquiv_mk]
    rfl

  have hmR : (maximalIdeal N).map j = maximalIdeal (UVCrossingModel W (π ^ E)) := by
    obtain ⟨e, -⟩ := quotEquiv (maximalIdeal N) 1 (by rw [pow_one])
    haveI := IsLocalRing.maximalIdeal.isMaximal N
    letI : Field (N ⧸ maximalIdeal N) := Ideal.Quotient.field (maximalIdeal N)
    haveI : IsField (UVCrossingModel W (π ^ E) ⧸ (maximalIdeal N).map j) :=
      MulEquiv.isField (Field.toIsField (N ⧸ maximalIdeal N)) e.symm.toMulEquiv
    exact IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField _ this)
  have hcπmem : const (π ^ E) π ∈ maximalIdeal (UVCrossingModel W (π ^ E)) := by
    rw [UVCrossingModel.maximalIdeal_eq_map_maximalIdeal_sup_span_pair hπEu]
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr hπu))
  have hϖm : ϖN ∈ maximalIdeal N := by
    rw [← purity (maximalIdeal N), Ideal.mem_comap, hmR, hjϖ]; exact hcπmem

  have hdimN := IsLocalRing.eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two ι
    (UVCrossingModel.ringKrullDim_le_two π hπ E hE)
  haveI : IsAdicComplete (maximalIdeal (UVCrossingModel W (π ^ E))) (UVCrossingModel W (π ^ E)) :=
    UVCrossingModel.isAdicComplete_maximalIdeal (π ^ E)
  have hdimR := IsLocalRing.eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two
    (AdicCompletion.ofAlgEquiv (maximalIdeal (UVCrossingModel W (π ^ E)))).symm.toRingEquiv
    (UVCrossingModel.ringKrullDim_le_two π hπ E hE)

  set J : Ideal (UVCrossingModel W (π ^ E)) := 𝔭.map j with hJ
  have hJ0 : J ≠ ⊥ := by
    intro h
    apply h𝔭0
    rw [← purity 𝔭, ← hJ, h, Ideal.comap_bot_of_injective j hjinj]
  have hJcomap : J.comap j = 𝔭 := purity 𝔭

  have hπQ : ∀ Q : Ideal (UVCrossingModel W (π ^ E)), Q.comap j = 𝔭 → const (π ^ E) π ∉ Q := by
    intro Q hQ h
    apply h𝔭ϖ
    rw [← hQ, Ideal.mem_comap, hjϖ]; exact h

  have min_to_over : ∀ Q ∈ J.minimalPrimes, Q.comap j = 𝔭 := by
    intro Q hQ
    haveI hQp : Q.IsPrime := hQ.1.1
    have hJQ : J ≤ Q := hQ.1.2
    have h𝔭le : 𝔭 ≤ Q.comap j := by rw [← hJcomap]; exact Ideal.comap_mono hJQ
    by_contra hne
    have hlt : 𝔭 < Q.comap j := lt_of_le_of_ne h𝔭le (Ne.symm hne)

    have hQm : Q.comap j = maximalIdeal N := by
      by_contra hne'
      exact h𝔭0 (hdimN 𝔭 (Q.comap j) inferInstance inferInstance hne' hlt)

    have hQmR : Q = maximalIdeal (UVCrossingModel W (π ^ E)) := by
      refine le_antisymm (IsLocalRing.le_maximalIdeal hQp.ne_top) ?_
      rw [← hmR, ← hQm]; exact Ideal.map_comap_le

    have hrad : J.radical = maximalIdeal (UVCrossingModel W (π ^ E)) := by
      rw [Ideal.radical_eq_sInf]
      refine le_antisymm ?_ (le_sInf fun P hP => ?_)
      · exact sInf_le ⟨hQmR ▸ hJQ, IsLocalRing.maximalIdeal.isMaximal _ |>.isPrime⟩
      · have hPle : P ≤ maximalIdeal _ := IsLocalRing.le_maximalIdeal hP.2.ne_top
        have := hQ.2 ⟨hP.2, hP.1⟩ (hQmR ▸ hPle)
        exact hQmR ▸ this
    obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (le_of_eq hrad.symm)
      ((isNoetherianRing_iff_ideal_fg _).mp inferInstance _)
    have : maximalIdeal N ^ k ≤ 𝔭 := by
      rw [← hJcomap, ← Ideal.map_le_iff_le_comap, Ideal.map_pow, hmR]; exact hk
    exact h𝔭ϖ (Ideal.IsPrime.le_of_pow_le this hϖm)

  have over_to_min : ∀ Q : Ideal (UVCrossingModel W (π ^ E)), Q.IsPrime → Q.comap j = 𝔭 → Q ∈ J.minimalPrimes := by
    intro Q hQp hQ
    refine ⟨⟨hQp, Ideal.map_le_iff_le_comap.mpr (le_of_eq hQ.symm)⟩, fun P ⟨hPp, hJP⟩ hPQ => ?_⟩
    have hQm : Q ≠ maximalIdeal _ := fun h => hπQ Q hQ (h ▸ hcπmem)
    have hP0 : P ≠ ⊥ := fun h => hJ0 (le_bot_iff.mp (h ▸ hJP))
    rcases eq_or_lt_of_le hPQ with h | h
    · exact le_of_eq h.symm
    · exact absurd (hdimR P Q hPp hQp hQm h) hP0

  have hfin : {Q : PrimeSpectrum (UVCrossingModel W (π ^ E)) | Q.asIdeal.comap j = 𝔭}.Finite := by
    refine (Set.Finite.preimage (f := PrimeSpectrum.asIdeal) (fun _ _ _ _ h => PrimeSpectrum.ext h)
      (Ideal.finite_minimalPrimes_of_isNoetherianRing _ J)).subset ?_
    intro Q hQ
    exact over_to_min Q.asIdeal Q.isPrime hQ
  set 𝓠 : Finset (PrimeSpectrum (UVCrossingModel W (π ^ E))) := hfin.toFinset with h𝓠
  have hmem𝓠 : ∀ Q, Q ∈ 𝓠 ↔ Q.asIdeal.comap j = 𝔭 := fun Q => by
    rw [h𝓠, Set.Finite.mem_toFinset]; rfl
  have hLHS : (∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal.comap j = 𝔭),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞)) =
      ∑ Q ∈ 𝓠, (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) := by
    rw [finsum_eq_sum_of_support_subset (s := 𝓠)]
    · refine Finset.sum_congr rfl fun Q hQ => ?_
      rw [finsum_eq_if, if_pos ((hmem𝓠 Q).mp hQ)]
    · intro Q hQ
      rw [Function.mem_support, finsum_eq_if] at hQ
      rw [Finset.mem_coe, hmem𝓠]
      by_contra h
      exact hQ (if_neg h)
  rw [hLHS]

  have hQfacts : ∀ Q ∈ 𝓠, Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧ J ≤ Q.asIdeal := fun Q hQ => by
    have h := (hmem𝓠 Q).mp hQ
    have hle : J ≤ Q.asIdeal := Ideal.map_le_iff_le_comap.mpr (le_of_eq h.symm)
    exact ⟨fun h0 => hJ0 (le_bot_iff.mp (h0 ▸ hle)), hπQ _ h, hle⟩
  haveI hfree : ∀ Q : ↥𝓠, Module.Free W (UVCrossingModel W (π ^ E) ⧸ Q.1.asIdeal) := fun Q =>
    (UVCrossingModel.free_and_finite_quotient_of_ne_bot_of_const_notMem π hπ E hE Q.1.asIdeal
      (hQfacts Q.1 Q.2).1 (hQfacts Q.1 Q.2).2.1).1
  haveI hfinQ : ∀ Q : ↥𝓠, Module.Finite W (UVCrossingModel W (π ^ E) ⧸ Q.1.asIdeal) := fun Q =>
    (UVCrossingModel.free_and_finite_quotient_of_ne_bot_of_const_notMem π hπ E hE Q.1.asIdeal
      (hQfacts Q.1 Q.2).1 (hQfacts Q.1 Q.2).2.1).2
  have h𝓠' : ∀ Q : PrimeSpectrum (UVCrossingModel W (π ^ E)), Q ∈ 𝓠 ↔ Q.asIdeal ∈ J.minimalPrimes :=
    fun Q => (hmem𝓠 Q).trans ⟨fun h => over_to_min Q.asIdeal Q.isPrime h, fun h => min_to_over _ h⟩
  have hJrad : J.IsRadical := (Ideal.isRadical_iff_quotient_reduced J).mpr hred
  have hsep : ∀ Q₀ ∈ 𝓠, ∃ n : ℕ, algebraMap W (UVCrossingModel W (π ^ E)) π ^ n ∈
      (𝓠.erase Q₀).inf PrimeSpectrum.asIdeal ⊔ Q₀.asIdeal := by
    intro Q₀ hQ₀
    set I : Ideal (UVCrossingModel W (π ^ E)) := (𝓠.erase Q₀).inf PrimeSpectrum.asIdeal with hI
    have hrad : maximalIdeal (UVCrossingModel W (π ^ E)) ≤ (I ⊔ Q₀.asIdeal).radical := by
      rw [Ideal.radical_eq_sInf]
      refine le_sInf fun P hP => ?_
      obtain ⟨hIP, hPp⟩ := hP
      obtain ⟨Q, hQ, hQP⟩ := (Ideal.IsPrime.inf_le' hPp).mp (le_sup_left.trans hIP)
      have hQ₀P : Q₀.asIdeal ≤ P := le_sup_right.trans hIP
      obtain ⟨hQne, hQmem⟩ := Finset.mem_erase.mp hQ
      by_contra hPm
      have hPne : P ≠ maximalIdeal _ := fun h => hPm (le_of_eq h.symm)
      have hlt : Q₀.asIdeal < P := by
        refine lt_of_le_of_ne hQ₀P fun h => hQne ?_
        have hQ₀min := over_to_min Q₀.asIdeal Q₀.isPrime ((hmem𝓠 _).mp hQ₀)
        have hle : Q.asIdeal ≤ Q₀.asIdeal := h ▸ hQP
        exact PrimeSpectrum.ext (le_antisymm hle (hQ₀min.2 ⟨Q.isPrime, (hQfacts Q hQmem).2.2⟩ hle))
      exact (hQfacts Q₀ hQ₀).1 (hdimR Q₀.asIdeal P Q₀.isPrime hPp hPne hlt)
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
      ((isNoetherianRing_iff_ideal_fg _).mp inferInstance _)
    exact ⟨n, hn (Ideal.pow_mem_pow hcπmem n)⟩
  have hsplit : ∑ Q ∈ 𝓠, (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) =
      Module.finrank W (UVCrossingModel W (π ^ E) ⧸ J) := by
    rw [← Nat.cast_sum, ← (Module.finrank_quotient_eq_sum_finrank_quotient_of_isRadical J hJrad 𝓠 h𝓠' π
      hπ.ne_zero hsep).2.2]

  have hrank : (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ J) : ℕ∞) =
      Module.length N (N ⧸ (𝔭 ⊔ Ideal.span {ϖN})) := by
    set I' : Ideal N := 𝔭 ⊔ Ideal.span {ϖN} with hI'

    have hradI' : maximalIdeal N ≤ I'.radical := by
      rw [Ideal.radical_eq_sInf]
      refine le_sInf fun P hP => ?_
      obtain ⟨hIP, hPp⟩ := hP
      have h𝔭P : 𝔭 ≤ P := le_sup_left.trans hIP
      have hϖP : ϖN ∈ P := hIP (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      by_contra hPm
      have hPne : P ≠ maximalIdeal N := fun h => hPm (le_of_eq h.symm)
      have hlt : 𝔭 < P := lt_of_le_of_ne h𝔭P (fun h => h𝔭ϖ (h.symm ▸ hϖP))
      exact h𝔭0 (hdimN 𝔭 P inferInstance hPp hPne hlt)
    obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hradI' hmNfg
    obtain ⟨e, he⟩ := quotEquiv I' k hk
    have hJ' : I'.map j = J ⊔ Ideal.span {const (π ^ E) π} := by
      rw [hI', Ideal.map_sup, Ideal.map_span, Set.image_singleton, hjϖ]
    have hkR : maximalIdeal (UVCrossingModel W (π ^ E)) ^ k ≤ I'.map j := by
      rw [← hmR, ← Ideal.map_pow]; exact Ideal.map_mono hk

    obtain ⟨hTfin, hTtf, -⟩ := Module.finrank_quotient_eq_sum_finrank_quotient_of_isRadical J hJrad 𝓠 h𝓠' π
      hπ.ne_zero hsep
    haveI := hTfin
    haveI := hTtf
    haveI hTfree : Module.Free W (UVCrossingModel W (π ^ E) ⧸ J) := Module.free_of_finite_type_torsion_free'

    have h1 := Module.finrank_eq_length_quotient_maximalIdeal_smul_top (W := W) (UVCrossingModel W (π ^ E) ⧸ J)
    have h2 := Module.length_quotient_smul_top_quotient (maximalIdeal W) J
    have hmWmap : (maximalIdeal W).map (algebraMap W (UVCrossingModel W (π ^ E))) = Ideal.span {const (π ^ E) π} := by
      rw [hmW, Ideal.map_span, Set.image_singleton]; rfl
    rw [hmWmap, ← hJ'] at h2

    have hflR : IsFiniteLength (UVCrossingModel W (π ^ E)) (UVCrossingModel W (π ^ E) ⧸ I'.map j) :=
      IsLocalRing.isFiniteLength_quotient_of_pow_le _ hkR
    have hsurjW : Function.Surjective ((residue (UVCrossingModel W (π ^ E))).comp
        (algebraMap W (UVCrossingModel W (π ^ E)))) := by
      intro x
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
      obtain ⟨w, hw⟩ := UVCrossingModel.exists_sub_const_mem_maximalIdeal hπEu x
      refine ⟨w, ?_⟩
      rw [RingHom.comp_apply]
      refine (Ideal.Quotient.eq (I := maximalIdeal (UVCrossingModel W (π ^ E)))).mpr ?_
      rw [← neg_mem_iff, neg_sub]
      exact hw
    have h3 : Module.length W (UVCrossingModel W (π ^ E) ⧸ I'.map j) =
        Module.length (UVCrossingModel W (π ^ E)) (UVCrossingModel W (π ^ E) ⧸ I'.map j) :=
      Module.length_restrictScalars_eq_of_surjective_residue hsurjW hflR

    letI algNR : Algebra N (UVCrossingModel W (π ^ E)) := j.toAlgebra
    have hsurjN : Function.Surjective ((residue (UVCrossingModel W (π ^ E))).comp
        (algebraMap N (UVCrossingModel W (π ^ E)))) := by
      intro x
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
      obtain ⟨e₁, he₁⟩ := quotEquiv (maximalIdeal N) 1 (by rw [pow_one])
      obtain ⟨n, hn⟩ := Ideal.Quotient.mk_surjective (e₁.symm (Ideal.Quotient.mk _ x))
      refine ⟨n, ?_⟩
      have : e₁ (Ideal.Quotient.mk _ n) = Ideal.Quotient.mk _ x := by rw [hn, RingEquiv.apply_symm_apply]
      rw [he₁, Ideal.Quotient.eq, hmR] at this
      rw [RingHom.comp_apply]
      exact (Ideal.Quotient.eq (I := maximalIdeal (UVCrossingModel W (π ^ E)))).mpr this
    have h4 : Module.length N (UVCrossingModel W (π ^ E) ⧸ I'.map j) =
        Module.length (UVCrossingModel W (π ^ E)) (UVCrossingModel W (π ^ E) ⧸ I'.map j) :=
      Module.length_restrictScalars_eq_of_surjective_residue hsurjN hflR

    let eN : (N ⧸ I') ≃ₗ[N] (UVCrossingModel W (π ^ E) ⧸ I'.map j) :=
      { e.toAddEquiv with
        map_smul' := fun n q => by
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
          change e (n • Ideal.Quotient.mk I' x) = n • e (Ideal.Quotient.mk I' x)
          have hl : n • Ideal.Quotient.mk I' x = Ideal.Quotient.mk I' (n * x) := by
            rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
          rw [hl, he, he, map_mul]
          have hr : n • j x = j n * j x := by
            rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
          rw [← hr]
          exact (Submodule.Quotient.mk_smul (Ideal.map j I') n (j x)).symm }
    rw [h1, h2, h3, ← h4, eN.length_eq]
  rw [hsplit, hrank]

end BCore

p2m_open "AlgebraicCurve IsLocalRing P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finsum_finrank_quotient_eq_length_of_comap_eq.IsLocalRing ModularCurve ModularCurve.UVCrossingModel"

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]

    (S : Set (Place L F))
    (hrat : ∀ P ∈ S, P.IsRational)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]

    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))

    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F))

    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)

    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))

    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (𝔭 : Ideal ↥𝒩₀) [𝔭.IsPrime] (h𝔭0 : 𝔭 ≠ ⊥) (h𝔭ϖ : (⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ : ↥𝒩₀) ∉ 𝔭) :
    ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
        (_ : Ideal.comap ((ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ →+* UVCrossingModel W (π ^ E)).comp
                (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀))) Q.asIdeal = 𝔭),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) =
      Module.length ↥𝒩₀ (↥𝒩₀ ⧸ (𝔭 ⊔ Ideal.span {(⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ : ↥𝒩₀)})) := by
  have hϖN : ι (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
      (⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ : ↥𝒩₀)) = const (π ^ E) π := by
    rw [← hσπ, hconst]
  exact finsum_finrank_quotient_eq_length_core π hπ E hE ι _ hϖN 𝔭 h𝔭0 h𝔭ϖ
    (AlgebraicCurve.NodeAnnulusEngine.isReduced_quotient_map_of_ne_bot_of_not_mem
      A S hrat 𝒩₀ hS hgen C hC hCmem ϖ hϖ hϖ0 halg hld hrk hres π hπ σ hσπ E hE ι hconst 𝔭 h𝔭0 h𝔭ϖ)

end S_AlgebraicCurve_NodeAnnulusEngine_finsum_finrank_quotient_eq_length_of_comap_eq
end P2MW
export P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finsum_finrank_quotient_eq_length_of_comap_eq (solution)

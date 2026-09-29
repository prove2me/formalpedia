-- Prove2me | solution 1 for ArtinL.Abelian.apply_idelicArtinMap_eq_one_of_isAdjuster_of_forall_valued_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/8039a85f-fb9e-5222-945e-df6c6e3079a0

import Mathlib
import Definitions.Def_ArtinL_Abelian
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_SIdeleClassGroup

import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_sub_algebraMap_mem_adicCompletionIntegers
import Theorems.Thm_NumberField_exists_ne_zero_and_sub_one_mem_and_lt_zero_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_Abelian_apply_idelicArtinMap_eq_one_of_isAdjuster_of_forall_valued_eq_one

set_option autoImplicit false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2.Artin
open M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
open scoped IsMulCommutative

universe u v

namespace ArtinL
namespace T1lg
p2m_open "ArtinL"
p2m_open "IsDedekindDomain NumberField NumberField.InfinitePlace.NumberField HeckeCharacter LanglandsTunnell.P2.Artin M4aHerbrand"

variable (K : Type u) [Field K] [NumberField K]

theorem snd_algebraMap_apply (a : K) (w : HeightOneSpectrum (𝓞 K)) :
    Valued.v (((algebraMap K (AdeleRing (𝓞 K) K) a).2 : FiniteAdeleRing (𝓞 K) K) w) = w.valuation K a := by
  change Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) a) w) = _
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem archRealProjTau_algebraMap (τ : K →+* ℝ) (a : Kˣ) :
    archRealProjTau K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) = τ a := by
  unfold archRealProjTau
  change InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_placeOf K τ)
      ((a : K) : (placeOf K τ).Completion) = τ a
  have h1 : InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_placeOf K τ) ((a : K) : (placeOf K τ).Completion) =
      InfinitePlace.Completion.extensionEmbeddingOfIsReal (isReal_placeOf K τ) ((a : K) : (placeOf K τ).Completion) := rfl
  rw [h1, InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply]
  change (InfinitePlace.mk (Complex.ofRealHom.comp τ)).embedding (a : K) = _
  rw [InfinitePlace.embedding_mk_eq_of_isReal (isReal_compOfRealHom K τ)]
  rfl

theorem archSign_algebraMap_iff (τ : K →+* ℝ) (a : Kˣ) :
    archSign K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) ↔ 0 < τ a := by
  unfold archSign
  rw [archRealProjTau_algebraMap]

theorem placeOrd_projFin (x : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    placeOrd K (projFin K x) w = -WithZero.log (Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w)) := rfl

theorem dvd_span_of_forall_pow_count_dvd {R : Type*} [CommRing R] [IsDedekindDomain R] {I : Ideal R} (hI : I ≠ ⊥) {r : R}
    (h : ∀ w : HeightOneSpectrum R, w.asIdeal ^ (Associates.mk w.asIdeal).count (Associates.mk I).factors ∣ Ideal.span {r}) :
    I ∣ Ideal.span {r} := by
  classical
  rw [← Ideal.finprod_heightOneSpectrum_factorization hI]

  rw [finprod_eq_prod _ (Ideal.finite_mulSupport hI)]
  refine Finset.prod_dvd_of_coprime ?_ fun w _ => h w
  intro w _ w' _ hne
  exact (Ideal.isCoprime_iff_sup_eq.2 ((w.isMaximal.coprime_of_ne w'.isMaximal
    (fun heq => hne (HeightOneSpectrum.ext heq))))).pow

theorem v_algebraMap (w : HeightOneSpectrum (𝓞 K)) (k : K) :
    Valued.v (algebraMap K (w.adicCompletion K) k) = w.valuation K k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w k

theorem snd_inv_apply (x : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    (((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w =
      ((((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  have h : (((x * x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 =
      ((x : AdeleRing (𝓞 K) K)).2 * (((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 := Prod.snd_mul _ _
  rw [← fad_mul_apply, ← h, mul_inv_cancel, Units.val_one]
  exact fad_one_apply K w

theorem snd_mul_apply (x y : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    (((x * y : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w =
      (((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w * (((y : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w := by
  have h : (((x * y : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 =
      ((x : AdeleRing (𝓞 K) K)).2 * ((y : AdeleRing (𝓞 K) K)).2 := Prod.snd_mul _ _
  rw [h, fad_mul_apply]

theorem algebraMap_fad_apply (k : K) (w : HeightOneSpectrum (𝓞 K)) :
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) k) w = algebraMap K (w.adicCompletion K) k := by
  rw [FiniteAdeleRing.algebraMap_apply]; rfl

end ArtinL.T1lg

theorem solution
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (ψ : (L ≃ₐ[K] L) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (𝔪' : Ideal (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔪')
    (N : ℕ)
    (hN : ∀ (β : 𝓞 K) (hβ : β ≠ 0) (𝔪 : Ideal (𝓞 K)) (hc : principalUnit K β hβ ∈ coprimeToModulus K 𝔪),
      (∀ τ : K →+* ℝ, 0 < τ (β : K)) → β - 1 ∈ v.asIdeal ^ N * 𝔪' →
        ψ (artinSymbol K L 𝔪 ⟨principalUnit K β hβ, hc⟩) = 1)

    (𝔣 : Ideal (𝓞 K)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree K L (Module.finrank K L) 𝔣)
    (r : (AdeleRing (𝓞 K) K)ˣ →* (L ≃ₐ[K] L))
    (hr₁ : principalIdeles (𝓞 K) K ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 K) K ⊔ (genuineBaseChange K L).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 K) K)ˣ, IsAdjuster K 𝔣 u 1 →
      r u = ∏ᶠ w : HeightOneSpectrum (𝓞 K), artinFrob K L w ^ placeOrd K (projFin K u) w)

    (x : (AdeleRing (𝓞 K) K)ˣ) (hx1 : IsAdjuster K (v.asIdeal ^ N * 𝔪') x 1)
    (hxinf : infPart x = 1)
    (hxu : ∀ w : HeightOneSpectrum (𝓞 K), Valued.v ((((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w) = 1) :
    ψ (r x) = 1 := by
  classical

  set 𝔤 : Ideal (𝓞 K) := v.asIdeal ^ N * 𝔪' with h𝔤def
  have h𝔪'0 : 𝔪' ≠ ⊥ := fun h => hv (h ▸ dvd_zero _)
  have h𝔤0 : 𝔤 ≠ ⊥ := mul_ne_zero (pow_ne_zero _ v.ne_bot) h𝔪'0
  have h𝔣0 : 𝔣 ≠ ⊥ := hadm.1
  let cnt : Ideal (𝓞 K) → HeightOneSpectrum (𝓞 K) → ℕ := fun I w => (Associates.mk w.asIdeal).count (Associates.mk I).factors
  have hcnt_dvd : ∀ (I : Ideal (𝓞 K)) (w : HeightOneSpectrum (𝓞 K)), I ≠ ⊥ → cnt I w ≠ 0 → w.asIdeal ∣ I := by
    intro I w hI hc
    have := (Associates.le_of_count_ne_zero (Associates.mk_ne_zero.2 hI) (Associates.irreducible_mk.2 w.irreducible) hc)
    rwa [Associates.mk_le_mk_iff_dvd] at this

  have hfinS : {w : HeightOneSpectrum (𝓞 K) | w.asIdeal ∣ 𝔣 * 𝔤}.Finite := Ideal.finite_factors (mul_ne_zero h𝔣0 h𝔤0)
  obtain ⟨S, hvS, hS𝔣, hS𝔤, hSdvd⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), v ∈ S ∧
      (∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ 𝔣 → w ∈ S) ∧ (∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ 𝔤 → w ∈ S) ∧
      (∀ w ∈ S, w.asIdeal ∣ 𝔣 * 𝔤 * v.asIdeal) := by
    refine ⟨insert v hfinS.toFinset, Finset.mem_insert_self _ _,
      fun w hw => Finset.mem_insert_of_mem (hfinS.mem_toFinset.2 (Dvd.dvd.mul_right hw _)),
      fun w hw => Finset.mem_insert_of_mem (hfinS.mem_toFinset.2 (Dvd.dvd.mul_left hw _)), fun w hw => ?_⟩
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact dvd_mul_left _ _
    · exact Dvd.dvd.mul_right (hfinS.mem_toFinset.1 hw) _
  obtain ⟨M, hM𝔣, hM𝔤, hM1⟩ : ∃ M : ℕ, (∀ w ∈ S, cnt 𝔣 w ≤ M) ∧ (∀ w ∈ S, cnt 𝔤 w ≤ M) ∧ 1 ≤ M :=
    ⟨1 + S.sup (fun w => cnt 𝔣 w + cnt 𝔤 w),
      fun w hw => (Nat.le_add_right _ _).trans ((Finset.le_sup (f := fun w => cnt 𝔣 w + cnt 𝔤 w) hw).trans (Nat.le_add_left _ _)),
      fun w hw => (Nat.le_add_left _ _).trans ((Finset.le_sup (f := fun w => cnt 𝔣 w + cnt 𝔤 w) hw).trans (Nat.le_add_left _ _)),
      Nat.le_add_right _ _⟩
  have hexpM : ∀ n : ℕ, n ≤ M → WithZero.exp (-(M : ℤ)) ≤ WithZero.exp (-(n : ℤ)) := fun n hn =>
    WithZero.exp_le_exp.2 (by omega)
  have hexpM1 : WithZero.exp (-(M : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

  have hxinf : ((x : AdeleRing (𝓞 K) K).1) = 1 := by
    have := congrArg Units.val hxinf
    exact this
  have hxunit : ∀ w : HeightOneSpectrum (𝓞 K), Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1 := hxu
  have hxcong : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ 𝔤 →
      Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w - 1) ≤ WithZero.exp (-(cnt 𝔤 w : ℤ)) := by
    intro w hw
    simpa using (hx1.cong w hw).2

  obtain ⟨𝔥, h𝔥0, h𝔥w⟩ : ∃ 𝔥 : Ideal (𝓞 K), 𝔥 ≠ ⊥ ∧
      ∀ w ∈ S, ∀ z : 𝓞 K, z ∈ 𝔥 → w.intValuation z ≤ WithZero.exp (-(M : ℤ)) := by
    refine ⟨(𝔣 * 𝔤 * v.asIdeal) ^ M, pow_ne_zero _ (mul_ne_zero (mul_ne_zero h𝔣0 h𝔤0) v.ne_bot), fun w hw z hz => ?_⟩
    have h1 : w.asIdeal ^ M ∣ (𝔣 * 𝔤 * v.asIdeal) ^ M := pow_dvd_pow_of_dvd (hSdvd w hw) M
    have h2 : (𝔣 * 𝔤 * v.asIdeal) ^ M ∣ Ideal.span {z} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hz)
    exact (HeightOneSpectrum.intValuation_le_pow_iff_dvd w z M).2 (h1.trans h2)
  obtain ⟨π, hπ𝔥, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔥0
  have hπK : (π : K) ≠ 0 := fun h => hπ0 (by exact_mod_cast h)

  obtain ⟨x₀, hx₀⟩ := IsDedekindDomain.FiniteAdeleRing.exists_sub_algebraMap_mem_adicCompletionIntegers K
    ((((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) * algebraMap K (FiniteAdeleRing (𝓞 K) K) (π : K)⁻¹)
  have ht_close : ∀ w : HeightOneSpectrum (𝓞 K),
      Valued.v ((((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w - algebraMap K (w.adicCompletion K) (π * x₀)) ≤
        w.valuation K (π : K) := by
    intro w
    have h1 := hx₀ w
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, fad_mul_apply] at h1
    have hπw : (algebraMap K (FiniteAdeleRing (𝓞 K) K) (π : K)⁻¹) w = (algebraMap K (w.adicCompletion K) (π : K))⁻¹ := by
      rw [ArtinL.T1lg.algebraMap_fad_apply, map_inv₀]
    rw [hπw] at h1
    have hπw0 : algebraMap K (w.adicCompletion K) (π : K) ≠ 0 := by
      rw [ne_eq, map_eq_zero]; exact hπK
    have : (((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w - algebraMap K (w.adicCompletion K) (π * x₀) =
        algebraMap K (w.adicCompletion K) (π : K) *
          ((((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w * (algebraMap K (w.adicCompletion K) (π : K))⁻¹ -
            algebraMap K (w.adicCompletion K) x₀) := by
      rw [mul_sub, mul_left_comm, mul_inv_cancel₀ hπw0, mul_one, map_mul]
    rw [this, map_mul, ArtinL.T1lg.v_algebraMap]
    exact mul_le_of_le_one_right' h1

  have ht_int : ∀ w : HeightOneSpectrum (𝓞 K), w.valuation K ((π : K) * x₀) ≤ 1 := by
    intro w
    have h1 := ht_close w
    have hπ1 : w.valuation K (π : K) ≤ 1 := by rw [HeightOneSpectrum.valuation_of_algebraMap]; exact w.intValuation_le_one π
    rw [← ArtinL.T1lg.v_algebraMap K w]
    have := Valuation.map_sub Valued.v ((((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w)
      (((((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w) - algebraMap K (w.adicCompletion K) ((π : K) * x₀))
    rw [sub_sub_cancel, hxunit w] at this
    exact this.trans (max_le le_rfl (h1.trans hπ1))
  obtain ⟨t, ht⟩ : ∃ t : 𝓞 K, (t : K) = (π : K) * x₀ := by
    obtain ⟨t, ht⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K ((π : K) * x₀) ht_int
    exact ⟨t, ht⟩

  obtain ⟨δ, hδ0, hδ1, hδsign⟩ := NumberField.exists_ne_zero_and_sub_one_mem_and_lt_zero_iff K 𝔥 h𝔥0
    {φ : K →+* ℝ | φ (t : K) < 0}
  set α : 𝓞 K := t * δ with hαdef
  have htK : (t : K) = (π : K) * x₀ := ht
  have hαK' : (α : K) = (t : K) * (δ : K) := by rw [hαdef]; push_cast; rfl

  have hvt : ∀ w ∈ S, Valued.v (algebraMap K (w.adicCompletion K) (t : K)) = 1 := by
    intro w hw
    have h1 : Valued.v ((((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w - algebraMap K (w.adicCompletion K) (t : K)) < 1 := by
      rw [htK]
      refine (ht_close w).trans_lt ?_
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (h𝔥w w hw π hπ𝔥).trans_lt hexpM1
    rw [← hxunit w]
    refine Valuation.map_eq_of_sub_lt Valued.v ?_
    rw [Valuation.map_sub_swap, hxunit w]
    exact h1
  have ht0 : t ≠ 0 := by
    intro h
    have := hvt v hvS
    rw [h, show ((0 : 𝓞 K) : K) = 0 from rfl, map_zero, map_zero] at this
    exact zero_ne_one this
  have hvδ1 : ∀ w ∈ S, Valued.v (algebraMap K (w.adicCompletion K) (δ : K) - 1) ≤ WithZero.exp (-(M : ℤ)) := by
    intro w hw
    have : algebraMap K (w.adicCompletion K) (δ : K) - 1 = algebraMap K (w.adicCompletion K) (((δ - 1 : 𝓞 K)) : K) := by
      rw [show (((δ - 1 : 𝓞 K)) : K) = (δ : K) - 1 by push_cast; rfl, map_sub, map_one]
    rw [this, ArtinL.T1lg.v_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact h𝔥w w hw _ hδ1
  have hα_close : ∀ w ∈ S,
      Valued.v ((((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w - algebraMap K (w.adicCompletion K) (α : K)) ≤
        WithZero.exp (-(M : ℤ)) := by
    intro w hw
    have h1 : Valued.v ((((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w - algebraMap K (w.adicCompletion K) (t : K)) ≤
        WithZero.exp (-(M : ℤ)) := by
      rw [htK]
      refine (ht_close w).trans ?_
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact h𝔥w w hw π hπ𝔥
    have h2 : Valued.v (algebraMap K (w.adicCompletion K) (t : K) - algebraMap K (w.adicCompletion K) (α : K)) ≤ WithZero.exp (-(M : ℤ)) := by
      have : algebraMap K (w.adicCompletion K) (t : K) - algebraMap K (w.adicCompletion K) (α : K) =
          algebraMap K (w.adicCompletion K) (t : K) * -(algebraMap K (w.adicCompletion K) (δ : K) - 1) := by
        rw [hαK', map_mul]; ring
      rw [this, map_mul, Valuation.map_neg, hvt w hw, one_mul]
      exact hvδ1 w hw
    have := Valuation.map_add Valued.v
      ((((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w - algebraMap K (w.adicCompletion K) (t : K))
      (algebraMap K (w.adicCompletion K) (t : K) - algebraMap K (w.adicCompletion K) (α : K))
    rw [sub_add_sub_cancel] at this
    exact this.trans (max_le h1 h2)
  have hvα : ∀ w ∈ S, Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = 1 := by
    intro w hw
    rw [← hxunit w]
    refine Valuation.map_eq_of_sub_lt Valued.v ?_
    rw [Valuation.map_sub_swap, hxunit w]
    exact (hα_close w hw).trans_lt hexpM1
  have hα0 : α ≠ 0 := mul_ne_zero ht0 hδ0
  have hαK : (α : K) ≠ 0 := fun h => hα0 (by exact_mod_cast h)

  have hpos : ∀ τ : K →+* ℝ, 0 < τ (α : K) := by
    intro τ
    have htτ : τ (t : K) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff τ τ.injective]; exact_mod_cast ht0
    have hδτ : τ (δ : K) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff τ τ.injective]; exact_mod_cast hδ0
    have hmul : τ (α : K) = τ (t : K) * τ (δ : K) := by rw [hαK', map_mul]
    rw [hmul]
    rcases lt_or_gt_of_ne htτ with h | h
    · exact mul_pos_of_neg_of_neg h ((hδsign τ).2 h)
    · have : ¬ τ (δ : K) < 0 := fun h' => (lt_irrefl _ (((hδsign τ).1 h').trans h))
      exact mul_pos h (lt_of_le_of_ne (not_lt.1 this) (Ne.symm hδτ))

  set d : (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 (α : K) hαK) with hddef
  have hd2 : ∀ w : HeightOneSpectrum (𝓞 K), (((d : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w = algebraMap K (w.adicCompletion K) (α : K) := by
    intro w
    rw [hddef, Units.coe_map, Units.val_mk0]
    exact ArtinL.T1lg.algebraMap_fad_apply K (α : K) w
  have hdker : r d = 1 := by
    have : d ∈ principalIdeles (𝓞 K) K := ⟨Units.mk0 (α : K) hαK, rfl⟩
    exact hr₁ this
  set y : (AdeleRing (𝓞 K) K)ˣ := x * d⁻¹ with hydef
  have hy2 : ∀ w : HeightOneSpectrum (𝓞 K), (((y : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w =
      (((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w * (algebraMap K (w.adicCompletion K) (α : K))⁻¹ := by
    intro w
    rw [hydef, ArtinL.T1lg.snd_mul_apply, ArtinL.T1lg.snd_inv_apply, hd2]
  have hαw0 : ∀ w : HeightOneSpectrum (𝓞 K), algebraMap K (w.adicCompletion K) (α : K) ≠ 0 := fun w => by
    rw [ne_eq, map_eq_zero]; exact hαK
  have hyadj : IsAdjuster K 𝔣 y 1 := by
    refine ⟨fun w hw => ?_, fun τ => ?_⟩
    · have hwS := hS𝔣 w hw
      rw [map_one, inv_one, mul_one, hy2]
      refine ⟨?_, ?_⟩
      · rw [map_mul, map_inv₀, hxunit w, hvα w hwS, inv_one, mul_one]
      · have : (((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w * (algebraMap K (w.adicCompletion K) (α : K))⁻¹ - 1 =
            ((((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w - algebraMap K (w.adicCompletion K) (α : K)) *
              (algebraMap K (w.adicCompletion K) (α : K))⁻¹ := by
          rw [sub_mul, mul_inv_cancel₀ (hαw0 w)]
        rw [this, map_mul, map_inv₀, hvα w hwS, inv_one, mul_one]
        exact (hα_close w hwS).trans (hexpM _ (hM𝔣 w hwS))
    · rw [map_one, inv_one, mul_one, hydef]
      refine (archSign_mul K τ x d⁻¹).2 (iff_of_true (archSign_of_fst_eq_one K τ hxinf) ?_)
      rw [archSign_inv, hddef, ArtinL.T1lg.archSign_algebraMap_iff]
      exact hpos τ

  have hry := hr₄ y hyadj
  have hord : ∀ w : HeightOneSpectrum (𝓞 K), placeOrd K (projFin K y) w = -(cnt (Ideal.span {α}) w : ℤ) := by
    intro w
    rw [ArtinL.T1lg.placeOrd_projFin, hy2, map_mul, map_inv₀, hxunit w, one_mul, ArtinL.T1lg.v_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hα0, ← WithZero.exp_neg, neg_neg,
      WithZero.log_exp]
  have hry' : r y = (∏ᶠ w : HeightOneSpectrum (𝓞 K), artinFrob K L w ^ (cnt (Ideal.span {α}) w : ℤ))⁻¹ := by
    rw [hry, ← finprod_inv_distrib]
    exact finprod_congr fun w => by rw [hord, zpow_neg]

  have hα1 : α - 1 ∈ 𝔤 := by
    refine (Ideal.span_singleton_le_iff_mem _).1 (Ideal.dvd_iff_le.1 (ArtinL.T1lg.dvd_span_of_forall_pow_count_dvd h𝔤0 fun w => ?_))
    refine (HeightOneSpectrum.intValuation_le_pow_iff_dvd w (α - 1) (cnt 𝔤 w)).1 ?_
    by_cases hc0 : cnt 𝔤 w = 0
    · rw [hc0]; simpa using w.intValuation_le_one (α - 1)
    have hwS : w ∈ S := hS𝔤 w (hcnt_dvd 𝔤 w h𝔤0 hc0)
    have e1 : w.intValuation (α - 1) = Valued.v (algebraMap K (w.adicCompletion K) (α : K) - 1) := by
      rw [← HeightOneSpectrum.valuation_of_algebraMap (K := K), ← ArtinL.T1lg.v_algebraMap K w,
        ← map_one (algebraMap K (w.adicCompletion K)), ← map_sub]
      congr 2
    rw [e1]
    have := Valuation.map_add Valued.v
      (algebraMap K (w.adicCompletion K) (α : K) - (((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w)
      ((((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w - 1)
    rw [sub_add_sub_cancel] at this
    refine this.trans (max_le ?_ (hxcong w (hcnt_dvd 𝔤 w h𝔤0 hc0)))
    rw [Valuation.map_sub_swap]
    exact (hα_close w hwS).trans (hexpM _ (hM𝔤 w hwS))
  have hc : principalUnit K α hα0 ∈ coprimeToModulus K 𝔤 := principalUnit_mem_coprimeToModulus K hα0 hα1

  have hsym : artinSymbol K L 𝔤 ⟨principalUnit K α hα0, hc⟩ =
      ∏ᶠ w : HeightOneSpectrum (𝓞 K), artinFrob K L w ^ (cnt (Ideal.span {α}) w : ℤ) := by
    unfold artinSymbol
    rw [raySymbolHom_apply]
    change raySymbol K (artinFrob K L)
      ((principalUnit K α hα0 : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = _
    rw [principalUnit_val]
    unfold raySymbol
    refine finprod_congr fun w => ?_
    rw [FractionalIdeal.count_coe K w (show (Ideal.span {α} : Ideal (𝓞 K)) ≠ 0 from
      fun h => hα0 (Ideal.span_singleton_eq_bot.1 h))]

  have hkill := hN α hα0 𝔤 hc hpos hα1
  have hx : x = y * d := by rw [hydef, inv_mul_cancel_right]
  rw [hx, map_mul, hdker, mul_one, hry', ← hsym, map_inv, hkill, inv_one]

end S_ArtinL_Abelian_apply_idelicArtinMap_eq_one_of_isAdjuster_of_forall_valued_eq_one
end P2MW
export P2MW.S_ArtinL_Abelian_apply_idelicArtinMap_eq_one_of_isAdjuster_of_forall_valued_eq_one (solution)

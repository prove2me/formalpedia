-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_div_mem_unitBox_of_lintegral_orbital_doubleCoset_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/7b93a0b7-5c6e-5c26-9f49-386fae7a65ae

import Theorems.Thm_AutomorphicForm_exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero
import Theorems.Thm_AutomorphicForm_isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_norm_act_apply_eq_norm_apply
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_div_mem_unitBox_of_lintegral_orbital_doubleCoset_ne_zero
p2m_attr_erase "simp" "AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

namespace P2mKcSupportBox

theorem abs_log_prod_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ i ∈ s, |Real.log (f i)| ≤ M) :
    |Real.log (∏ i ∈ s, f i)| ≤ s.card * M := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have hs : |Real.log (∏ i ∈ s, f i)| ≤ s.card * M := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha' : |Real.log (f a)| ≤ M := h a (Finset.mem_insert_self a s)
    by_cases h0 : f a * ∏ i ∈ s, f i = 0
    · rw [h0, Real.log_zero, abs_zero]; push_cast; positivity
    · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h0
      rw [Real.log_mul h1 h2]
      calc |Real.log (f a) + Real.log (∏ i ∈ s, f i)|
          ≤ |Real.log (f a)| + |Real.log (∏ i ∈ s, f i)| := abs_add_le _ _
        _ ≤ M + s.card * M := add_le_add ha' hs
        _ = ((s.card + 1 : ℕ) : ℝ) * M := by push_cast; ring

section NormComparison

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem absNorm_under_le_absNorm (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.absNorm (HeightOneSpectrum.under (𝓞 K) w).asIdeal ≤ Ideal.absNorm w.asIdeal := by
  have hv : (HeightOneSpectrum.under (𝓞 K) w).asIdeal = w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) := rfl
  haveI : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine Nat.card_le_card_of_injective
    (Ideal.quotientMap w.asIdeal (algebraMap (𝓞 K) (𝓞 L)) (le_of_eq hv)) ?_
  exact Ideal.quotientMap_injective' (le_of_eq hv.symm)

theorem norm_adicCompletion_under (w : HeightOneSpectrum (𝓞 L)) (x : K) :
    (‖((algebraMap K L x : L) : w.adicCompletion L)‖ = 1 →
        ‖(x : (HeightOneSpectrum.under (𝓞 K) w).adicCompletion K)‖ = 1) ∧
    |Real.log ‖(x : (HeightOneSpectrum.under (𝓞 K) w).adicCompletion K)‖| ≤
      |Real.log ‖((algebraMap K L x : L) : w.adicCompletion L)‖| := by
  set v := HeightOneSpectrum.under (𝓞 K) w with hv_def

  have hbv1 : 1 < (Ideal.absNorm v.asIdeal : NNReal) := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  have hbw1 : 1 < (Ideal.absNorm w.asIdeal : NNReal) := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w
  have hle : (Ideal.absNorm v.asIdeal : NNReal) ≤ (Ideal.absNorm w.asIdeal : NNReal) := by
    exact_mod_cast absNorm_under_le_absNorm K L w
  set e := Ideal.ramificationIdx' v.asIdeal w.asIdeal with he_def
  have he : e ≠ 0 := HeightOneSpectrum.ramificationIdx_ne_zero (𝓞 K) (𝓞 L)
    (algebraMap_injective_of_field_isFractionRing (𝓞 K) (𝓞 L) K L) w

  have hnv0 : ‖(x : v.adicCompletion K)‖ =
      WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (v.valuation K x) :=
    NumberField.FinitePlace.norm_embedding' v x
  have hval : w.valuation L (algebraMap K L x) = v.valuation K x ^ e := by
    rw [← HeightOneSpectrum.valuation_comap (𝓞 K) K L (𝓞 L) w x]
  have hnw0 : ‖((algebraMap K L x : L) : w.adicCompletion L)‖ =
      WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero w) (w.valuation L (algebraMap K L x)) :=
    NumberField.FinitePlace.norm_embedding' w (algebraMap K L x)
  by_cases hx : x = 0
  · subst hx
    rw [hnv0, hnw0]
    simp
  have hm : v.valuation K x ≠ 0 := by
    rwa [Ne, Valuation.zero_iff]
  set z : ℤ := (WithZero.unzero hm).toAdd with hz
  set bv : ℝ := ((Ideal.absNorm v.asIdeal : NNReal) : ℝ) with hbv
  set bw : ℝ := ((Ideal.absNorm w.asIdeal : NNReal) : ℝ) with hbw
  have hnv : ‖(x : v.adicCompletion K)‖ = bv ^ z := by
    rw [hnv0, WithZeroMulInt.toNNReal_neg_apply _ hm, NNReal.coe_zpow]
  have hnw : ‖((algebraMap K L x : L) : w.adicCompletion L)‖ = (bw ^ z) ^ e := by
    rw [hnw0, hval, map_pow, WithZeroMulInt.toNNReal_neg_apply _ hm, NNReal.coe_pow, NNReal.coe_zpow]
  rw [hnv, hnw]
  have hbv1' : 1 < bv := by rw [hbv]; exact_mod_cast hbv1
  have hbw1' : 1 < bw := by rw [hbw]; exact_mod_cast hbw1
  have hlv : 0 < Real.log bv := Real.log_pos hbv1'
  have hlw : 0 < Real.log bw := Real.log_pos hbw1'
  have hlvw : Real.log bv ≤ Real.log bw :=
    Real.log_le_log (by linarith) (by rw [hbv, hbw]; exact_mod_cast hle)
  have hlogv : Real.log (bv ^ z) = z * Real.log bv := Real.log_zpow _ _
  have hlogw : Real.log ((bw ^ z) ^ e) = e * (z * Real.log bw) := by
    rw [Real.log_pow, Real.log_zpow]
  refine ⟨fun h1 => ?_, ?_⟩
  ·
    have h1' : Real.log ((bw ^ z) ^ e) = 0 := by rw [h1, Real.log_one]
    rw [hlogw] at h1'
    have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he
    have hz0 : (z : ℝ) = 0 := by
      rcases mul_eq_zero.mp h1' with h | h
      · exact absurd h he'
      · rcases mul_eq_zero.mp h with h | h
        · exact h
        · exact absurd h hlw.ne'
    have hz0' : z = 0 := by exact_mod_cast hz0
    rw [hz0', zpow_zero]
  · rw [hlogv, hlogw, abs_mul, abs_mul, abs_mul]
    have he1 : (1 : ℝ) ≤ |(e : ℝ)| := by
      rw [Nat.abs_cast]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr he
    calc |(z : ℝ)| * |Real.log bv| ≤ |(z : ℝ)| * |Real.log bw| := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [abs_of_pos hlv, abs_of_pos hlw]; exact hlvw
      _ = 1 * (|(z : ℝ)| * |Real.log bw|) := (one_mul _).symm
      _ ≤ |(e : ℝ)| * (|(z : ℝ)| * |Real.log bw|) :=
          mul_le_mul_of_nonneg_right he1 (by positivity)

theorem norm_adicCompletion_of_extension (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) (x : K) :
    (‖((algebraMap K L x : L) : w.1.adicCompletion L)‖ = 1 → ‖(x : v.adicCompletion K)‖ = 1) ∧
    |Real.log ‖(x : v.adicCompletion K)‖| ≤
      |Real.log ‖((algebraMap K L x : L) : w.1.adicCompletion L)‖| := by
  obtain ⟨w, rfl⟩ := w
  exact norm_adicCompletion_under K L w x

end NormComparison

section Iterate

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem exists_norm_iterate_act_snd_eq (i : ℕ) (a : AdeleRing (𝓞 L) L)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) :
    ∃ w' : v.Extension (𝓞 L),
      ‖((⇑(D.act σ : RingAut (AdeleRing (𝓞 L) L)))^[i] a).2 w.1‖ = ‖a.2 w'.1‖ := by
  induction i generalizing w with
  | zero => exact ⟨w, rfl⟩
  | succ i ih =>
    obtain ⟨w', hw'⟩ := (M4aHerbrand.IdeleGaloisDescent.exists_norm_act_apply_eq_norm_apply K L D σ
      ((⇑(D.act σ : RingAut (AdeleRing (𝓞 L) L)))^[i] a)).1 v w
    obtain ⟨w'', hw''⟩ := ih w'
    exact ⟨w'', by rw [Function.iterate_succ_apply', hw', hw'']⟩

theorem exists_norm_iterate_act_fst_eq (i : ℕ) (a : AdeleRing (𝓞 L) L) (w : InfinitePlace L) :
    ∃ w' : InfinitePlace L,
      ‖((⇑(D.act σ : RingAut (AdeleRing (𝓞 L) L)))^[i] a).1 w‖ = ‖a.1 w'‖ := by
  induction i generalizing w with
  | zero => exact ⟨w, rfl⟩
  | succ i ih =>
    obtain ⟨w', hw'⟩ := (M4aHerbrand.IdeleGaloisDescent.exists_norm_act_apply_eq_norm_apply K L D σ
      ((⇑(D.act σ : RingAut (AdeleRing (𝓞 L) L)))^[i] a)).2 w
    obtain ⟨w'', hw''⟩ := ih w'
    exact ⟨w'', by rw [Function.iterate_succ_apply', hw', hw'']⟩

theorem iterate_act_mul (i : ℕ) (a b : AdeleRing (𝓞 L) L) :
    (⇑(D.act σ : RingAut (AdeleRing (𝓞 L) L)))^[i] (a * b) =
      (⇑(D.act σ : RingAut (AdeleRing (𝓞 L) L)))^[i] a * (⇑(D.act σ : RingAut (AdeleRing (𝓞 L) L)))^[i] b := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      map_mul]

theorem isUnit_iterate_act (i : ℕ) {a : AdeleRing (𝓞 L) L} (ha : IsUnit a) :
    IsUnit ((⇑(D.act σ : RingAut (AdeleRing (𝓞 L) L)))^[i] a) := by
  induction i with
  | zero => exact ha
  | succ i ih => rw [Function.iterate_succ_apply']; exact ih.map _

theorem prod_snd_apply {ι : Type*} (s : Finset ι) (f : ι → AdeleRing (𝓞 L) L) (w : HeightOneSpectrum (𝓞 L)) :
    (∏ i ∈ s, f i).2 w = ∏ i ∈ s, (f i).2 w := by
  have : ∀ a : AdeleRing (𝓞 L) L, a.2 w = ((finAdeleEval (𝓞 L) L w).comp (adeleFin (𝓞 L) L)) a := fun _ => rfl
  simp_rw [this, map_prod]

theorem prod_fst_apply {ι : Type*} (s : Finset ι) (f : ι → AdeleRing (𝓞 L) L) (w : InfinitePlace L) :
    (∏ i ∈ s, f i).1 w = ∏ i ∈ s, (f i).1 w := by
  have : ∀ a : AdeleRing (𝓞 L) L, a.1 w = ((archEval L w).comp (adeleArch (𝓞 L) L)) a := fun _ => rfl
  simp_rw [this, map_prod]

end Iterate

end P2mKcSupportBox

namespace P2mKcSupportBox

section Cyclic

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem norm_algebraMap_snd_eq_prod {A B : AdeleRing (𝓞 L) L} (hA : IsUnit A) (x₀ : K)
    (hprod : ∏ i ∈ Finset.range (Module.finrank K L), (⇑(D.act σ : RingAut (AdeleRing (𝓞 L) L)))^[i] B =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L x₀) *
        ∏ i ∈ Finset.range (Module.finrank K L), (⇑(D.act σ : RingAut (AdeleRing (𝓞 L) L)))^[i] A)
    (v : HeightOneSpectrum (𝓞 K)) (w₀ : v.Extension (𝓞 L)) :
    ∃ ws' : ℕ → v.Extension (𝓞 L),
      ‖((algebraMap K L x₀ : L) : w₀.1.adicCompletion L)‖ =
        ∏ i ∈ Finset.range (Module.finrank K L),
          ‖((B.2 (ws' i).1 : (ws' i).1.adicCompletion L) / (A.2 (ws' i).1 : (ws' i).1.adicCompletion L))‖ := by
  classical
  set f : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L := ⇑(D.act σ : RingAut (AdeleRing (𝓞 L) L)) with hf
  set lam : AdeleRing (𝓞 L) L := B * ↑(hA.unit⁻¹) with hlam

  have hunit : IsUnit (∏ i ∈ Finset.range (Module.finrank K L), f^[i] A) :=
    Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun i _ => isUnit_iterate_act K L D σ i hA)
  have hkey : ∏ i ∈ Finset.range (Module.finrank K L), f^[i] lam =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L x₀) := by
    have h1 : (∏ i ∈ Finset.range (Module.finrank K L), f^[i] lam) *
        ∏ i ∈ Finset.range (Module.finrank K L), f^[i] A =
        ∏ i ∈ Finset.range (Module.finrank K L), f^[i] B := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← iterate_act_mul K L D σ]
      congr 1
      rw [hlam, mul_assoc, IsUnit.val_inv_mul, mul_one]
    rw [hprod] at h1
    exact (IsUnit.mul_left_inj hunit).mp h1

  choose ws' hws' using fun i => exists_norm_iterate_act_snd_eq K L D σ i lam v w₀
  refine ⟨ws', ?_⟩
  have hcoord : ((algebraMap K L x₀ : L) : w₀.1.adicCompletion L) =
      (algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L x₀)).2 w₀.1 := rfl
  rw [hcoord, ← hkey, prod_snd_apply, norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hws' i]

  have hAw : (A.2 (ws' i).1 : (ws' i).1.adicCompletion L) * ((↑(hA.unit⁻¹) : AdeleRing (𝓞 L) L).2 (ws' i).1) = 1 := by
    have h2 := congrArg (fun a : AdeleRing (𝓞 L) L => a.2 (ws' i).1) (IsUnit.mul_val_inv hA)
    exact h2
  have hAne : (A.2 (ws' i).1 : (ws' i).1.adicCompletion L) ≠ 0 := left_ne_zero_of_mul_eq_one hAw
  have hinv : ((↑(hA.unit⁻¹) : AdeleRing (𝓞 L) L).2 (ws' i).1) = (A.2 (ws' i).1 : (ws' i).1.adicCompletion L)⁻¹ :=
    eq_inv_of_mul_eq_one_right hAw
  rw [hlam]
  show ‖(B * ↑(hA.unit⁻¹)).2 (ws' i).1‖ = _
  rw [show (B * ↑(hA.unit⁻¹)).2 (ws' i).1 = B.2 (ws' i).1 * ((↑(hA.unit⁻¹) : AdeleRing (𝓞 L) L).2 (ws' i).1)
    from rfl, hinv, div_eq_mul_inv]

theorem norm_algebraMap_fst_eq_prod {A B : AdeleRing (𝓞 L) L} (hA : IsUnit A) (x₀ : K)
    (hprod : ∏ i ∈ Finset.range (Module.finrank K L), (⇑(D.act σ : RingAut (AdeleRing (𝓞 L) L)))^[i] B =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L x₀) *
        ∏ i ∈ Finset.range (Module.finrank K L), (⇑(D.act σ : RingAut (AdeleRing (𝓞 L) L)))^[i] A)
    (w₀ : InfinitePlace L) :
    ∃ ws' : ℕ → InfinitePlace L,
      ‖((algebraMap K L x₀ : L) : w₀.Completion)‖ =
        ∏ i ∈ Finset.range (Module.finrank K L),
          ‖((B.1 (ws' i) : (ws' i).Completion) / (A.1 (ws' i) : (ws' i).Completion))‖ := by
  classical
  set f : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L := ⇑(D.act σ : RingAut (AdeleRing (𝓞 L) L)) with hf
  set lam : AdeleRing (𝓞 L) L := B * ↑(hA.unit⁻¹) with hlam
  have hunit : IsUnit (∏ i ∈ Finset.range (Module.finrank K L), f^[i] A) :=
    Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun i _ => isUnit_iterate_act K L D σ i hA)
  have hkey : ∏ i ∈ Finset.range (Module.finrank K L), f^[i] lam =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L x₀) := by
    have h1 : (∏ i ∈ Finset.range (Module.finrank K L), f^[i] lam) *
        ∏ i ∈ Finset.range (Module.finrank K L), f^[i] A =
        ∏ i ∈ Finset.range (Module.finrank K L), f^[i] B := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← iterate_act_mul K L D σ]
      congr 1
      rw [hlam, mul_assoc, IsUnit.val_inv_mul, mul_one]
    rw [hprod] at h1
    exact (IsUnit.mul_left_inj hunit).mp h1
  choose ws' hws' using fun i => exists_norm_iterate_act_fst_eq K L D σ i lam w₀
  refine ⟨ws', ?_⟩
  have hcoord : ((algebraMap K L x₀ : L) : w₀.Completion) =
      (algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L x₀)).1 w₀ := rfl
  rw [hcoord, ← hkey, prod_fst_apply, norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hws' i]
  have hAw : (A.1 (ws' i) : (ws' i).Completion) * ((↑(hA.unit⁻¹) : AdeleRing (𝓞 L) L).1 (ws' i)) = 1 := by
    have h2 := congrArg (fun a : AdeleRing (𝓞 L) L => a.1 (ws' i)) (IsUnit.mul_val_inv hA)
    exact h2
  have hinv : ((↑(hA.unit⁻¹) : AdeleRing (𝓞 L) L).1 (ws' i)) = (A.1 (ws' i) : (ws' i).Completion)⁻¹ :=
    eq_inv_of_mul_eq_one_right hAw
  rw [hlam]
  show ‖(B * ↑(hA.unit⁻¹)).1 (ws' i)‖ = _
  rw [show (B * ↑(hA.unit⁻¹)).1 (ws' i) = B.1 (ws' i) * ((↑(hA.unit⁻¹) : AdeleRing (𝓞 L) L).1 (ws' i))
    from rfl, hinv, div_eq_mul_inv]

end Cyclic

end P2mKcSupportBox

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in
open AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

    (Δ : Set (GL (Fin 2) L))
    (hΔd : ∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (hΔdisj : ∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)),
      ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∃ cS cinf : ℝ,
      ∀ (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v) →
      ∀ t ∈ Δ,
        (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) ≠ 0 →
        Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0 ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S ∪ T →
          ‖(algebraMap K (v.adicCompletion K)
            (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1)))‖ = 1) ∧
        (∀ v ∈ T,
          |Real.log ‖(algebraMap K (v.adicCompletion K)
            (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1)))‖| ≤
            A₀ * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal)) ∧
        (∀ v ∈ S, v ∉ T →
          |Real.log ‖(algebraMap K (v.adicCompletion K)
            (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1)))‖| ≤ cS) ∧
        (∀ w : NumberField.InfinitePlace K,
          |Real.log (w (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1)))| ≤ cinf) := by
  classical
  intro T ws
  obtain ⟨A₀, hA₀, cS, cinf, hW⟩ :=
    AutomorphicForm.exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero
      K L D σ hgen S φa φS T ws
  set n : ℕ := Module.finrank K L with hn_def
  refine ⟨n * A₀, by positivity, n * cS, n * cinf, ?_⟩
  intro ρ φ φf hfac t ht hne
  obtain ⟨ht10, ht01, hN1⟩ := hΔd t ht

  set r : K := Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) with hr_def
  set x₀ : K := Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0) with hx₀_def

  have hdet : (t : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
    have hu : IsUnit (t : Matrix (Fin 2) (Fin 2) L).det := by
      rw [Matrix.isUnit_iff_isUnit_det _ |>.symm]; exact Units.isUnit t
    exact hu.ne_zero
  have ht00 : (t : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
    intro h; apply hdet; rw [Matrix.det_fin_two, h, ht10]; ring
  have ht11 : (t : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
    intro h; apply hdet; rw [Matrix.det_fin_two, h, ht01]; ring
  have hr0 : r ≠ 0 := by
    rw [hr_def, Ne, Algebra.norm_eq_zero_iff]
    exact div_ne_zero ht00 ht11
  have hx0r : x₀ = r⁻¹ := by
    have hmul : r * x₀ = 1 := by
      rw [hr_def, hx₀_def, ← map_mul, div_mul_div_cancel₀ ht11, div_self ht00, map_one]
    exact (eq_inv_of_mul_eq_one_right hmul)

  obtain ⟨x, z, hxz⟩ : ∃ (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ≠ 0 := by
    by_contra hall
    simp only [not_exists, ne_eq, not_not] at hall
    apply hne
    simp_rw [hall]
    simp

  obtain ⟨b, k, hb, hk1, hk2, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq L x
  have hk : k ∈ AutomorphicForm.adelicMaximalCompact L :=
    AutomorphicForm.mem_adelicMaximalCompact_iff.mpr ⟨hk1, hk2⟩

  set gp : AdelicGL2 (𝓞 L) L := b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) with hgp
  set A : AdeleRing (𝓞 L) L := (gp : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 with hA
  set B : AdeleRing (𝓞 L) L := (gp : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 with hB
  set E : AdeleRing (𝓞 L) L := (gp : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 with hE

  obtain ⟨hoff, hT, hSmT, hinf⟩ := hW ρ φ φf hfac t ht10 ht01 b hb k hk z hxz A B E hA.symm hB.symm hE.symm
  obtain ⟨⟨hAu, -⟩, -, hprod, -⟩ :=
    AutomorphicForm.isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal
      K L D σ hgen t ht10 ht01 b hb z A B E hA.symm hB.symm hE.symm

  have hfin : ∀ (v : HeightOneSpectrum (𝓞 K)) (M : ℝ), 0 ≤ M →
      (∀ w : v.Extension (𝓞 L),
        |Real.log ‖((B.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖| ≤ M) →
      |Real.log ‖(algebraMap K (v.adicCompletion K) r)‖| ≤ n * M := by
    intro v M hM hw
    obtain ⟨ws', hws'⟩ := P2mKcSupportBox.norm_algebraMap_snd_eq_prod K L D σ hAu x₀ hprod v (ws v)
    have h1 : |Real.log ‖((algebraMap K L x₀ : L) : (ws v).1.adicCompletion L)‖| ≤ n * M := by
      rw [hws']
      have := P2mKcSupportBox.abs_log_prod_le (Finset.range n) _ M hM (fun i _ => hw (ws' i))
      simpa [Finset.card_range] using this
    have h2 := (P2mKcSupportBox.norm_adicCompletion_of_extension K L v (ws v) x₀).2
    have h3 : |Real.log ‖(x₀ : v.adicCompletion K)‖| ≤ n * M := h2.trans h1
    have h4 : algebraMap K (v.adicCompletion K) r = (algebraMap K (v.adicCompletion K) x₀)⁻¹ := by
      rw [hx0r, map_inv₀, inv_inv]
    rw [h4, norm_inv, Real.log_inv, abs_neg]
    exact h3
  have hfin1 : ∀ (v : HeightOneSpectrum (𝓞 K)),
      (∀ w : v.Extension (𝓞 L),
        ‖((B.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖ = 1) →
      ‖(algebraMap K (v.adicCompletion K) r)‖ = 1 := by
    intro v hw
    obtain ⟨ws', hws'⟩ := P2mKcSupportBox.norm_algebraMap_snd_eq_prod K L D σ hAu x₀ hprod v (ws v)
    have h1 : ‖((algebraMap K L x₀ : L) : (ws v).1.adicCompletion L)‖ = 1 := by
      rw [hws']
      exact Finset.prod_eq_one fun i _ => hw (ws' i)
    have h2 := (P2mKcSupportBox.norm_adicCompletion_of_extension K L v (ws v) x₀).1 h1
    have h4 : algebraMap K (v.adicCompletion K) r = (algebraMap K (v.adicCompletion K) x₀)⁻¹ := by
      rw [hx0r, map_inv₀, inv_inv]
    rw [h4, norm_inv]
    have h2' : ‖algebraMap K (v.adicCompletion K) x₀‖ = 1 := h2
    rw [h2', inv_one]
  have harch : ∀ w : NumberField.InfinitePlace K, |Real.log (w r)| ≤ n * cinf := by
    intro w
    obtain ⟨w', hw'⟩ := NumberField.InfinitePlace.comap_surjective (k := K) (K := L) w
    obtain ⟨ws', hws'⟩ := P2mKcSupportBox.norm_algebraMap_fst_eq_prod K L D σ hAu x₀ hprod w'
    have hM : 0 ≤ cinf := (abs_nonneg _).trans (hinf w').1
    have h1 : |Real.log ‖((algebraMap K L x₀ : L) : w'.Completion)‖| ≤ n * cinf := by
      rw [hws']
      have := P2mKcSupportBox.abs_log_prod_le (Finset.range n) _ cinf hM (fun i _ => (hinf (ws' i)).1)
      simpa [Finset.card_range] using this
    have h2 : ‖((algebraMap K L x₀ : L) : w'.Completion)‖ = w x₀ := by
      rw [← hw', NumberField.InfinitePlace.comap_apply]
      exact NumberField.InfinitePlace.Completion.norm_coe (v := w') (WithAbs.toAbs w'.1 (algebraMap K L x₀))
    rw [h2, hx0r, map_inv₀, Real.log_inv, abs_neg] at h1
    exact h1
  refine ⟨hr0, fun v hv => hfin1 v fun w => (hoff v hv w).1, fun v hv => ?_, fun v hvS hvT => ?_, harch⟩
  ·
    have hM : 0 ≤ A₀ * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
        (semiLocalIntegralSet K L v *
          {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
            semiLocalIntegralSet K L v)).toReal) :=
      (abs_nonneg _).trans (hT v hv (ws v)).1
    have := hfin v _ hM fun w => (hT v hv w).1
    calc _ ≤ _ := this
      _ = _ := by rw [hn_def]; ring
  ·
    have hM : 0 ≤ cS := (abs_nonneg _).trans (hSmT v hvS hvT (ws v)).1
    exact hfin v cS hM fun w => (hSmT v hvS hvT w).1

end S_AutomorphicForm_exists_forall_norm_div_mem_unitBox_of_lintegral_orbital_doubleCoset_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_div_mem_unitBox_of_lintegral_orbital_doubleCoset_ne_zero (solution)

-- Prove2me | solution 1 for AutomorphicForm.exists_forall_abs_log_adelicHeight_mul_adelicHeight_adelicWeyl_le_mul_prod_pow_log_measure_of_doubleCoset_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/758b6221-4a35-5346-82ce-c820c63b882b

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_NumberField_AdelicHeight_neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_eq_unipotentGL2_of_mem_adelicBorel
import Theorems.Thm_NumberField_AdelicHeight_neg_log_adelicHeight_unipotentGL2_sub_log_adelicHeight_adelicWeyl_mul_unipotentGL2_eq
import Theorems.Thm_AutomorphicForm_exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero
import Theorems.Thm_AutomorphicForm_isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal
import Theorems.Thm_RingHom_one_sub_prod_iterate_mul_eq_sum_prod_iterate_mul_iterate_of_apply_eq_mul_add
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_norm_act_apply_eq_norm_apply
import Theorems.Thm_NumberField_sum_mult_mul_log_one_add_norm_sq_add_two_mul_finsum_log_max_norm_le_of_one_sub_mul_eq_sum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_abs_log_adelicHeight_mul_adelicHeight_adelicWeyl_le_mul_prod_pow_log_measure_of_doubleCoset_apply_ne_zero
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar semiLocalHaar_semiLocalIntegralSet semiLocalComponent IsSemiLocalFactorization AdelicGL2 globalPoints centralScalar sigmaAdelicAct adelicWeyl adelicMaximalCompact mem_adelicMaximalCompact_iff exists_mem_adelicBorel_mul_eq exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal"
namespace ExcursionAssembly
p2m_open "AutomorphicForm"

section Generic

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem snd_mul_apply (a b : AdeleRing (𝓞 L) L) (w : HeightOneSpectrum (𝓞 L)) :
    (a * b).2 w = a.2 w * b.2 w := rfl

theorem fst_mul_apply (a b : AdeleRing (𝓞 L) L) (w : InfinitePlace L) :
    (a * b).1 w = a.1 w * b.1 w := rfl

theorem snd_one_apply (w : HeightOneSpectrum (𝓞 L)) : (1 : AdeleRing (𝓞 L) L).2 w = 1 := rfl

theorem fst_one_apply (w : InfinitePlace L) : (1 : AdeleRing (𝓞 L) L).1 w = 1 := rfl

theorem norm_snd_mul_unit_inv (A B : AdeleRing (𝓞 L) L) (hA : IsUnit A) (w : HeightOneSpectrum (𝓞 L)) :
    ‖(B * ↑hA.unit⁻¹).2 w‖ = ‖(B.2 w : w.adicCompletion L) / (A.2 w : w.adicCompletion L)‖ := by
  have h2 : (A.2 w) * ((↑hA.unit⁻¹ : AdeleRing (𝓞 L) L).2 w) = 1 := by
    rw [← snd_mul_apply, hA.mul_val_inv, snd_one_apply]
  rw [snd_mul_apply, div_eq_mul_inv, ← eq_inv_of_mul_eq_one_right h2]

theorem norm_fst_mul_unit_inv (A B : AdeleRing (𝓞 L) L) (hA : IsUnit A) (w : InfinitePlace L) :
    ‖(B * ↑hA.unit⁻¹).1 w‖ = ‖(B.1 w : w.Completion) / (A.1 w : w.Completion)‖ := by
  have h2 : (A.1 w) * ((↑hA.unit⁻¹ : AdeleRing (𝓞 L) L).1 w) = 1 := by
    rw [← fst_mul_apply, hA.mul_val_inv, fst_one_apply]
  rw [fst_mul_apply, div_eq_mul_inv, ← eq_inv_of_mul_eq_one_right h2]

omit K L in
theorem le_exp_of_abs_log_le (x b : ℝ) (hx : 0 ≤ x) (h : |Real.log x| ≤ b) : x ≤ Real.exp b := by
  rcases hx.eq_or_lt with h0 | h0
  · rw [← h0]; exact (Real.exp_pos b).le
  · calc x = Real.exp (Real.log x) := (Real.exp_log h0).symm
      _ ≤ Real.exp b := Real.exp_le_exp.mpr ((le_abs_self _).trans h)

omit K L in
theorem le_exp_of_posLog_le (x b : ℝ) (hx : 0 ≤ x) (h : Real.posLog x ≤ b) : x ≤ Real.exp b := by
  rcases hx.eq_or_lt with h0 | h0
  · rw [← h0]; exact (Real.exp_pos b).le
  · calc x = Real.exp (Real.log x) := (Real.exp_log h0).symm
      _ ≤ Real.exp b := Real.exp_le_exp.mpr ((le_max_right _ _).trans h)

omit K L in
theorem one_le_prod {ι : Type} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i :=
  Finset.prod_induction _ (fun x => 1 ≤ x) (fun _ _ ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl h

omit K L in
theorem le_prod_of_mem {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, 1 ≤ f i)
    (i : ι) (hi : i ∈ s) : f i ≤ ∏ j ∈ s, f j := by
  rw [← Finset.mul_prod_erase s f hi]
  have h1 : 1 ≤ ∏ j ∈ s.erase i, f j := one_le_prod _ _ fun j hj => h j (Finset.mem_of_mem_erase hj)
  have h0 : 0 ≤ f i := zero_le_one.trans (h i hi)
  nlinarith

omit K L in
theorem sum_le_card_mul_prod {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, 1 ≤ f i) :
    ∑ i ∈ s, f i ≤ s.card * ∏ j ∈ s, f j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, ∏ j ∈ s, f j := Finset.sum_le_sum fun i hi => le_prod_of_mem s f h i hi
    _ = s.card * ∏ j ∈ s, f j := by rw [Finset.sum_const, nsmul_eq_mul]

omit K L in
theorem iterate_map_mul {R : Type*} [CommRing R] (e : R ≃+* R) (n : ℕ) (a b : R) :
    (⇑e)^[n] (a * b) = (⇑e)^[n] a * (⇑e)^[n] b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_mul]

omit K L in
theorem iterate_map_one {R : Type*} [CommRing R] (e : R ≃+* R) (n : ℕ) : (⇑e)^[n] (1 : R) = 1 :=
  Function.iterate_fixed (map_one e) n

omit K L in
theorem prod_iterate_map_mul {R : Type*} [CommRing R] (e : R ≃+* R) (s : Finset ℕ) (a b : R) :
    ∏ i ∈ s, (⇑e)^[i] (a * b) = (∏ i ∈ s, (⇑e)^[i] a) * ∏ i ∈ s, (⇑e)^[i] b := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => iterate_map_mul e i a b

def FibreBound (g : HeightOneSpectrum (𝓞 K) → ℝ) (ginf : ℝ) (a : AdeleRing (𝓞 L) L) : Prop :=
  (∀ (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)), ‖a.2 w.1‖ ≤ g v) ∧
    ∀ w : InfinitePlace L, ‖a.1 w‖ ≤ ginf

variable {K L}

theorem FibreBound.act [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    {g : HeightOneSpectrum (𝓞 K) → ℝ} {ginf : ℝ} {a : AdeleRing (𝓞 L) L} (h : FibreBound K L g ginf a) :
    FibreBound K L g ginf ((D.act σ) a) := by
  obtain ⟨hf, hi⟩ := M4aHerbrand.IdeleGaloisDescent.exists_norm_act_apply_eq_norm_apply K L D σ a
  refine ⟨fun v w => ?_, fun w => ?_⟩
  · obtain ⟨w', hw'⟩ := hf v w
    rw [hw']; exact h.1 v w'
  · obtain ⟨w', hw'⟩ := hi w
    rw [hw']; exact h.2 w'

theorem FibreBound.iterate [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    {g : HeightOneSpectrum (𝓞 K) → ℝ} {ginf : ℝ} {a : AdeleRing (𝓞 L) L} (h : FibreBound K L g ginf a) (n : ℕ) :
    FibreBound K L g ginf ((⇑(D.act σ))^[n] a) := by
  induction n with
  | zero => exact h
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.act D σ

theorem FibreBound.mul {g g' : HeightOneSpectrum (𝓞 K) → ℝ} {ginf ginf' : ℝ} {a b : AdeleRing (𝓞 L) L}
    (ha : FibreBound K L g ginf a) (hb : FibreBound K L g' ginf' b) :
    FibreBound K L (g * g') (ginf * ginf') (a * b) := by
  refine ⟨fun v w => ?_, fun w => ?_⟩
  · rw [snd_mul_apply, norm_mul, Pi.mul_apply]
    exact mul_le_mul (ha.1 v w) (hb.1 v w) (norm_nonneg _) ((norm_nonneg _).trans (ha.1 v w))
  · rw [fst_mul_apply, norm_mul]
    exact mul_le_mul (ha.2 w) (hb.2 w) (norm_nonneg _) ((norm_nonneg _).trans (ha.2 w))

theorem FibreBound.one : FibreBound K L 1 1 (1 : AdeleRing (𝓞 L) L) :=
  ⟨fun v w => by rw [snd_one_apply, norm_one, Pi.one_apply], fun w => by rw [fst_one_apply, norm_one]⟩

theorem FibreBound.mono {g g' : HeightOneSpectrum (𝓞 K) → ℝ} {ginf ginf' : ℝ} {a : AdeleRing (𝓞 L) L}
    (ha : FibreBound K L g ginf a) (hg : ∀ v, g v ≤ g' v) (hginf : ginf ≤ ginf') :
    FibreBound K L g' ginf' a :=
  ⟨fun v w => (ha.1 v w).trans (hg v), fun w => (ha.2 w).trans hginf⟩

theorem FibreBound.prod_card {g : HeightOneSpectrum (𝓞 K) → ℝ} {ginf : ℝ}
    (s : Finset ℕ) (f : ℕ → AdeleRing (𝓞 L) L) (hf : ∀ i ∈ s, FibreBound K L g ginf (f i)) :
    FibreBound K L (g ^ s.card) (ginf ^ s.card) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (FibreBound.one (K := K) (L := L))
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ', pow_succ']
    exact (hf i (Finset.mem_insert_self i s)).mul (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem FibreBound.prod_pow {g : HeightOneSpectrum (𝓞 K) → ℝ} {ginf : ℝ} (hg : ∀ v, 1 ≤ g v) (hginf : 1 ≤ ginf)
    (s : Finset ℕ) (f : ℕ → AdeleRing (𝓞 L) L) (hf : ∀ i ∈ s, FibreBound K L g ginf (f i))
    (n : ℕ) (hn : s.card ≤ n) :
    FibreBound K L (g ^ n) (ginf ^ n) (∏ i ∈ s, f i) :=
  (FibreBound.prod_card s f hf).mono (fun v => by rw [Pi.pow_apply, Pi.pow_apply]; exact pow_le_pow_right₀ (hg v) hn)
    (pow_le_pow_right₀ hginf hn)

theorem FibreBound.apply_under {g : HeightOneSpectrum (𝓞 K) → ℝ} {ginf : ℝ} {a : AdeleRing (𝓞 L) L}
    (ha : FibreBound K L g ginf a) (w : HeightOneSpectrum (𝓞 L)) : ‖a.2 w‖ ≤ g (w.under (𝓞 K)) :=
  ha.1 (w.under (𝓞 K)) ⟨w, rfl⟩

end Generic

end AutomorphicForm.ExcursionAssembly

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar semiLocalHaar_semiLocalIntegralSet semiLocalComponent IsSemiLocalFactorization AdelicGL2 globalPoints centralScalar sigmaAdelicAct adelicWeyl adelicMaximalCompact mem_adelicMaximalCompact_iff exists_mem_adelicBorel_mul_eq exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal"
namespace ExcursionAssembly
p2m_open "AutomorphicForm"

section Core

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [DecidableEq (HeightOneSpectrum (𝓞 K))]

omit [DecidableEq (HeightOneSpectrum (𝓞 K))] in
theorem mem_preimageComapFinset_iff' (S : Finset (HeightOneSpectrum (𝓞 K))) (w : HeightOneSpectrum (𝓞 L)) :
    w ∈ IsDedekindDomain.HeightOneSpectrum.preimageComapFinset (𝓞 K) K L (𝓞 L) S ↔ w.under (𝓞 K) ∈ S := by
  simp [IsDedekindDomain.HeightOneSpectrum.preimageComapFinset]

theorem fibreBound_of_cases (S T : Finset (HeightOneSpectrum (𝓞 K))) (M cinf' : ℝ)
    (bT bS : HeightOneSpectrum (𝓞 K) → ℝ) (hbT : ∀ v ∈ T, bT v ≤ M) (hbS : ∀ v ∈ S, bS v ≤ M)
    (a : AdeleRing (𝓞 L) L)
    (hout : ∀ v, v ∉ S ∪ T → ∀ w : v.Extension (𝓞 L), ‖a.2 w.1‖ ≤ 1)
    (hT : ∀ v ∈ T, ∀ w : v.Extension (𝓞 L), ‖a.2 w.1‖ ≤ Real.exp (bT v))
    (hS : ∀ v ∈ S, v ∉ T → ∀ w : v.Extension (𝓞 L), ‖a.2 w.1‖ ≤ Real.exp (bS v))
    (hinf : ∀ w : InfinitePlace L, ‖a.1 w‖ ≤ Real.exp cinf') :
    FibreBound K L (fun v => Real.exp (if v ∈ S ∪ T then M else 0)) (Real.exp cinf') a := by
  refine ⟨fun v w => ?_, hinf⟩
  dsimp only
  by_cases hvT : v ∈ T
  · have h1 : v ∈ S ∪ T := Finset.mem_union_right S hvT
    rw [if_pos h1]
    exact (hT v hvT w).trans (Real.exp_le_exp.mpr (hbT v hvT))
  · by_cases hvS : v ∈ S
    · have h1 : v ∈ S ∪ T := Finset.mem_union_left T hvS
      rw [if_pos h1]
      exact (hS v hvS hvT w).trans (Real.exp_le_exp.mpr (hbS v hvS))
    · have h1 : v ∉ S ∪ T := by rw [Finset.mem_union, not_or]; exact ⟨hvS, hvT⟩
      rw [if_neg h1, Real.exp_zero]
      exact hout v h1 w

open IsDedekindDomain.HeightOneSpectrum in

theorem abs_excursion_le_of_windows [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (ℓ : ℕ)
    (A₀ cS' cinf' : ℝ) (hA₀ : 0 ≤ A₀) (hcS' : 0 ≤ cS') (hcinf' : 0 ≤ cinf')
    (m : HeightOneSpectrum (𝓞 K) → ℝ) (hm : ∀ v ∈ T, 1 ≤ m v)
    (x lam u : AdeleRing (𝓞 L) L) (c : L) (hc : c ≠ 1)
    (hσ : (D.act σ) x = lam * x + u) (hper : ∀ r : AdeleRing (𝓞 L) L, (⇑(D.act σ))^[ℓ] r = r)
    (hN : ∏ i ∈ Finset.range ℓ, (⇑(D.act σ))^[i] lam = algebraMap L (AdeleRing (𝓞 L) L) c)
    (hout : ∀ v, v ∉ S ∪ T → ∀ w : v.Extension (𝓞 L), ‖lam.2 w.1‖ ≤ 1 ∧ ‖u.2 w.1‖ ≤ 1)
    (hT : ∀ v ∈ T, ∀ w : v.Extension (𝓞 L),
      ‖lam.2 w.1‖ ≤ Real.exp (A₀ * m v) ∧ ‖u.2 w.1‖ ≤ Real.exp (A₀ * m v))
    (hS : ∀ v ∈ S, v ∉ T → ∀ w : v.Extension (𝓞 L), ‖lam.2 w.1‖ ≤ Real.exp cS' ∧ ‖u.2 w.1‖ ≤ Real.exp cS')
    (hinf : ∀ w : InfinitePlace L, ‖lam.1 w‖ ≤ Real.exp cinf' ∧ ‖u.1 w‖ ≤ Real.exp cinf') :
    |(∑ w : InfinitePlace L, (w.mult : ℝ) * Real.log (1 + ‖x.1 w‖ ^ 2)) +
        2 * ∑ᶠ v : HeightOneSpectrum (𝓞 L), Real.log (max 1 ‖x.2 v‖)| ≤
      ((2 * ℓ + 4) * ((preimageComapFinset (𝓞 K) K L (𝓞 L) (S ∪ T)).card * ℓ * (A₀ * T.card + cS') +
          (∑ w : InfinitePlace L, (w.mult : ℝ)) * ℓ * cinf') +
        (4 * Real.log 2 + 2 * Real.log ℓ) * ∑ w : InfinitePlace L, (w.mult : ℝ)) * ∏ v ∈ T, m v := by
  classical

  have hnonneg : 0 ≤ (∑ w : NumberField.InfinitePlace L, (w.mult : ℝ) * Real.log (1 + ‖x.1 w‖ ^ 2)) +
      2 * ∑ᶠ v : HeightOneSpectrum (𝓞 L), Real.log (max 1 ‖x.2 v‖) := by
    refine add_nonneg (Finset.sum_nonneg fun w _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by nlinarith [sq_nonneg ‖x.1 w‖]))) (mul_nonneg (by norm_num) (finsum_nonneg fun v => ?_))
    exact Real.log_nonneg (le_max_left _ _)
  rw [abs_of_nonneg hnonneg]

  have hℓ : ℓ ≠ 0 := by
    rintro rfl
    rw [Finset.prod_range_zero, ← map_one (algebraMap L (AdeleRing (𝓞 L) L))] at hN
    exact hc (NumberField.AdeleRing.algebraMap_injective (𝓞 L) L hN).symm

  set W := preimageComapFinset (𝓞 K) K L (𝓞 L) (S ∪ T) with hW
  set r : ℝ := ∑ w : InfinitePlace L, (w.mult : ℝ) with hr
  set Mtot : ℝ := ∑ v ∈ T, m v with hMtot
  set P : ℝ := ∏ v ∈ T, m v with hP
  have hm0 : ∀ v ∈ T, 0 ≤ m v := fun v hv => zero_le_one.trans (hm v hv)
  have hMtot0 : 0 ≤ Mtot := Finset.sum_nonneg hm0
  have hmle : ∀ v ∈ T, m v ≤ Mtot := fun v hv => Finset.single_le_sum hm0 hv
  have hP1 : 1 ≤ P := one_le_prod T m hm
  have hMtotP : Mtot ≤ T.card * P := sum_le_card_mul_prod T m hm
  have hr0 : 0 ≤ r := Finset.sum_nonneg fun w _ => Nat.cast_nonneg _
  have hℓ0 : 0 ≤ (ℓ : ℝ) := Nat.cast_nonneg _
  set M : ℝ := A₀ * Mtot + cS' with hM
  have hM0 : 0 ≤ M := add_nonneg (mul_nonneg hA₀ hMtot0) hcS'
  have hbT : ∀ v ∈ T, A₀ * m v ≤ M := fun v hv =>
    (mul_le_mul_of_nonneg_left (hmle v hv) hA₀).trans (le_add_of_nonneg_right hcS')
  have hbS : ∀ v ∈ S, cS' ≤ M := fun _ _ => le_add_of_nonneg_left (mul_nonneg hA₀ hMtot0)

  obtain ⟨gexp, hgexp⟩ : ∃ gexp : HeightOneSpectrum (𝓞 K) → ℝ, gexp = fun v => if v ∈ S ∪ T then M else 0 :=
    ⟨_, rfl⟩
  have hgexp0 : ∀ v, 0 ≤ gexp v := fun v => by
    rw [hgexp]; dsimp only; split_ifs; exacts [hM0, le_rfl]
  have hgexpM : ∀ v, gexp v ≤ M := fun v => by
    rw [hgexp]; dsimp only; split_ifs; exacts [le_rfl, hM0]
  obtain ⟨G, hG⟩ : ∃ G : HeightOneSpectrum (𝓞 K) → ℝ, G = fun v => Real.exp (gexp v) := ⟨_, rfl⟩
  have hG1 : ∀ v, 1 ≤ G v := fun v => by rw [hG]; exact Real.one_le_exp (hgexp0 v)
  have hGi1 : 1 ≤ Real.exp cinf' := Real.one_le_exp hcinf'
  have hlam : FibreBound K L G (Real.exp cinf') lam := by
    rw [hG, hgexp]
    exact fibreBound_of_cases S T M cinf' (fun v => A₀ * m v) (fun _ => cS') hbT hbS lam
      (fun v hv w => (hout v hv w).1) (fun v hv w => (hT v hv w).1) (fun v hv hv' w => (hS v hv hv' w).1)
      (fun w => (hinf w).1)
  have hu : FibreBound K L G (Real.exp cinf') u := by
    rw [hG, hgexp]
    exact fibreBound_of_cases S T M cinf' (fun v => A₀ * m v) (fun _ => cS') hbT hbS u
      (fun v hv w => (hout v hv w).2) (fun v hv w => (hT v hv w).2) (fun v hv hv' w => (hS v hv hv' w).2)
      (fun w => (hinf w).2)

  obtain ⟨Pf, hPf⟩ : ∃ Pf : ℕ → AdeleRing (𝓞 L) L,
      Pf = fun j => ∏ i ∈ Finset.Ico (j + 1) ℓ, (⇑(D.act σ))^[i] lam := ⟨_, rfl⟩
  obtain ⟨Uf, hUf⟩ : ∃ Uf : ℕ → AdeleRing (𝓞 L) L, Uf = fun j => (⇑(D.act σ))^[j] u := ⟨_, rfl⟩
  obtain ⟨Qf, hQf⟩ : ∃ Qf : ℕ → AdeleRing (𝓞 L) L, Qf = fun i => (⇑(D.act σ))^[i] lam := ⟨_, rfl⟩
  have hPb : ∀ j, FibreBound K L (G ^ ℓ) (Real.exp cinf' ^ ℓ) (Pf j) := fun j => by
    rw [hPf]
    exact FibreBound.prod_pow hG1 hGi1 _ _ (fun i _ => hlam.iterate D σ i) ℓ (by rw [Nat.card_Ico]; omega)
  have hUb : ∀ j, FibreBound K L (G ^ ℓ) (Real.exp cinf' ^ ℓ) (Uf j) := fun j => by
    rw [hUf]
    exact (hu.iterate D σ j).mono (fun v => by rw [Pi.pow_apply]; exact le_self_pow₀ (hG1 v) hℓ)
      (le_self_pow₀ hGi1 hℓ)
  have hQb : ∀ i, FibreBound K L (G ^ ℓ) (Real.exp cinf' ^ ℓ) (Qf i) := fun i => by
    rw [hQf]
    exact (hlam.iterate D σ i).mono (fun v => by rw [Pi.pow_apply]; exact le_self_pow₀ (hG1 v) hℓ)
      (le_self_pow₀ hGi1 hℓ)

  obtain ⟨Λ, hΛ⟩ : ∃ Λ : HeightOneSpectrum (𝓞 L) → ℝ, Λ = fun w => Real.exp (ℓ * gexp (w.under (𝓞 K))) :=
    ⟨_, rfl⟩
  obtain ⟨Λinf, hΛinf⟩ : ∃ Λinf : InfinitePlace L → ℝ, Λinf = fun _ => Real.exp (ℓ * cinf') := ⟨_, rfl⟩
  have hGΛ : ∀ w : HeightOneSpectrum (𝓞 L), (G ^ ℓ) (w.under (𝓞 K)) = Λ w := fun w => by
    rw [hΛ, hG, Pi.pow_apply, ← Real.exp_nat_mul]
  have hGΛinf : ∀ w : InfinitePlace L, Real.exp cinf' ^ ℓ = Λinf w := fun w => by
    rw [hΛinf, ← Real.exp_nat_mul]
  have conv : ∀ a : AdeleRing (𝓞 L) L, FibreBound K L (G ^ ℓ) (Real.exp cinf' ^ ℓ) a →
      (∀ w : HeightOneSpectrum (𝓞 L), ‖a.2 w‖ ≤ Λ w) ∧ ∀ w : InfinitePlace L, ‖a.1 w‖ ≤ Λinf w :=
    fun a ha => ⟨fun w => (hGΛ w) ▸ ha.apply_under w, fun w => (hGΛinf w) ▸ ha.2 w⟩
  have hΛ1 : ∀ w, 1 ≤ Λ w := fun w => by
    rw [hΛ]; exact Real.one_le_exp (mul_nonneg hℓ0 (hgexp0 _))
  have hΛW : ∀ w, w ∉ W → Λ w = 1 := fun w hw => by
    rw [mem_preimageComapFinset_iff'] at hw
    rw [hΛ]; dsimp only; rw [hgexp]; dsimp only; rw [if_neg hw, mul_zero, Real.exp_zero]
  have hΛinf1 : ∀ w, 1 ≤ Λinf w := fun w => by
    rw [hΛinf]; exact Real.one_le_exp (mul_nonneg hℓ0 hcinf')

  have key : (1 - ∏ i ∈ Finset.range ℓ, (⇑(D.act σ))^[i] lam) * x =
      ∑ j ∈ Finset.range ℓ, (∏ i ∈ Finset.Ico (j + 1) ℓ, (⇑(D.act σ))^[i] lam) * (⇑(D.act σ))^[j] u :=
    RingHom.one_sub_prod_iterate_mul_eq_sum_prod_iterate_mul_iterate_of_apply_eq_mul_add
      (AdeleRing (𝓞 L) L) (D.act σ).toRingHom ℓ hper x lam u hσ
  have hx : algebraMap L (AdeleRing (𝓞 L) L) (1 - c) * x = ∑ j ∈ Finset.range ℓ, Pf j * Uf j := by
    rw [map_sub, map_one, ← hN, hPf, hUf]; exact key
  have hcQ : algebraMap L (AdeleRing (𝓞 L) L) c = ∏ i ∈ Finset.range ℓ, Qf i := by rw [hQf]; exact hN.symm

  have hsum := NumberField.sum_mult_mul_log_one_add_norm_sq_add_two_mul_finsum_log_max_norm_le_of_one_sub_mul_eq_sum
    L c hc ℓ x Pf Uf Qf hx hcQ W Λ Λinf hΛ1 hΛW hΛinf1 (fun j _ => conv _ (hPb j)) (fun j _ => conv _ (hUb j))
    (fun i _ => conv _ (hQb i))

  have hlogΛ : ∑ w ∈ W, Real.log (Λ w) ≤ W.card * (ℓ * M) := by
    calc ∑ w ∈ W, Real.log (Λ w) ≤ ∑ w ∈ W, (ℓ * M : ℝ) := Finset.sum_le_sum fun w _ => by
            rw [hΛ]; dsimp only; rw [Real.log_exp]; exact mul_le_mul_of_nonneg_left (hgexpM _) hℓ0
      _ = W.card * (ℓ * M) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hlogΛinf : ∑ w : InfinitePlace L, (w.mult : ℝ) * Real.log (Λinf w) = r * (ℓ * cinf') := by
    rw [hΛinf]; dsimp only; rw [Real.log_exp, Finset.sum_mul]
  have hκ : 0 ≤ 4 * Real.log 2 + 2 * Real.log ℓ :=
    add_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg one_le_two))
      (mul_nonneg (by norm_num) (Real.log_natCast_nonneg ℓ))
  have h1 : (2 * ℓ + 4) * W.card * ℓ * A₀ * Mtot ≤ (2 * ℓ + 4) * W.card * ℓ * A₀ * (T.card * P) :=
    mul_le_mul_of_nonneg_left hMtotP (by positivity)
  have h2 : (2 * ℓ + 4) * (W.card * ℓ * cS' + r * ℓ * cinf') + (4 * Real.log 2 + 2 * Real.log ℓ) * r ≤
      ((2 * ℓ + 4) * (W.card * ℓ * cS' + r * ℓ * cinf') + (4 * Real.log 2 + 2 * Real.log ℓ) * r) * P :=
    le_mul_of_one_le_right (by positivity) hP1
  calc (∑ w : InfinitePlace L, (w.mult : ℝ) * Real.log (1 + ‖x.1 w‖ ^ 2)) +
        2 * ∑ᶠ v : HeightOneSpectrum (𝓞 L), Real.log (max 1 ‖x.2 v‖)
      ≤ (2 * ℓ + 4) * ((∑ w ∈ W, Real.log (Λ w)) + ∑ w : InfinitePlace L, (w.mult : ℝ) * Real.log (Λinf w)) +
        (4 * Real.log 2 + 2 * Real.log ℓ) * r := hsum
    _ ≤ (2 * ℓ + 4) * (W.card * (ℓ * M) + r * (ℓ * cinf')) + (4 * Real.log 2 + 2 * Real.log ℓ) * r := by
        rw [hlogΛinf]; gcongr
    _ ≤ ((2 * ℓ + 4) * (W.card * ℓ * (A₀ * T.card + cS') + r * ℓ * cinf') +
        (4 * Real.log 2 + 2 * Real.log ℓ) * r) * P := by
        rw [hM]; linarith [h1, h2]

end Core

end AutomorphicForm.ExcursionAssembly

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar semiLocalHaar_semiLocalIntegralSet semiLocalComponent IsSemiLocalFactorization AdelicGL2 globalPoints centralScalar sigmaAdelicAct adelicWeyl adelicMaximalCompact mem_adelicMaximalCompact_iff exists_mem_adelicBorel_mul_eq exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal"
namespace ExcursionAssembly
p2m_open "AutomorphicForm"

section Resolvent

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [DecidableEq (HeightOneSpectrum (𝓞 K))]

variable (K L) in
open IsDedekindDomain.HeightOneSpectrum in

noncomputable def excursionConstant (S T : Finset (HeightOneSpectrum (𝓞 K))) (A₀ cS' cinf' : ℝ) : ℝ :=
  ((2 * (Module.finrank K L) + 4) *
      ((preimageComapFinset (𝓞 K) K L (𝓞 L) (S ∪ T)).card * (Module.finrank K L) * (A₀ * T.card + cS') +
        (∑ w : InfinitePlace L, (w.mult : ℝ)) * (Module.finrank K L) * cinf') +
    (4 * Real.log 2 + 2 * Real.log (Module.finrank K L)) * ∑ w : InfinitePlace L, (w.mult : ℝ))

theorem excursionConstant_nonneg (S T : Finset (HeightOneSpectrum (𝓞 K))) (A₀ cS' cinf' : ℝ)
    (hA₀ : 0 ≤ A₀) (hcS' : 0 ≤ cS') (hcinf' : 0 ≤ cinf') : 0 ≤ excursionConstant K L S T A₀ cS' cinf' := by
  unfold excursionConstant
  have hr0 : 0 ≤ ∑ w : InfinitePlace L, (w.mult : ℝ) := Finset.sum_nonneg fun w _ => Nat.cast_nonneg _
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hlℓ : 0 ≤ Real.log (Module.finrank K L : ℕ) := Real.log_natCast_nonneg _
  positivity

theorem abs_excursion_le_of_resolvent [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (A₀ cS cinf : ℝ) (hA₀ : 0 ≤ A₀)
    (m : HeightOneSpectrum (𝓞 K) → ℝ) (hm : ∀ v ∈ T, 1 ≤ m v)
    (t : GL (Fin 2) L) (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hnorm : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (x A B E : AdeleRing (𝓞 L) L) (hAu : IsUnit A)
    (hres : A * (D.act σ) x = B * x + E)
    (hnormB : ∏ i ∈ Finset.range (Module.finrank K L), (⇑(D.act σ))^[i] B =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L
        (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0))) *
      ∏ i ∈ Finset.range (Module.finrank K L), (⇑(D.act σ))^[i] A)
    (hper : ∀ r : AdeleRing (𝓞 L) L, (⇑(D.act σ))^[Module.finrank K L] r = r)
    (hw : (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S ∪ T → ∀ w : v.Extension (𝓞 L),
            ‖((B.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖ = 1 ∧
            ‖((E.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖ ≤ 1) ∧
        (∀ v ∈ T, ∀ w : v.Extension (𝓞 L),
            |Real.log ‖((B.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖| ≤ A₀ * m v ∧
            Real.posLog ‖((E.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖ ≤ A₀ * m v) ∧
        (∀ v ∈ S, v ∉ T → ∀ w : v.Extension (𝓞 L),
            |Real.log ‖((B.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖| ≤ cS ∧
            Real.posLog ‖((E.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖ ≤ cS) ∧
        (∀ w : NumberField.InfinitePlace L,
            |Real.log ‖((B.1 w : w.Completion) / (A.1 w : w.Completion))‖| ≤ cinf ∧
            Real.posLog ‖((E.1 w : w.Completion) / (A.1 w : w.Completion))‖ ≤ cinf)) :
    |(∑ w : InfinitePlace L, (w.mult : ℝ) * Real.log (1 + ‖x.1 w‖ ^ 2)) +
        2 * ∑ᶠ v : HeightOneSpectrum (𝓞 L), Real.log (max 1 ‖x.2 v‖)| ≤
      excursionConstant K L S T A₀ (max cS 0) (max cinf 0) * ∏ v ∈ T, m v := by
  obtain ⟨hout, hT, hS, hinf⟩ := hw

  have hdet : ((t : Matrix (Fin 2) (Fin 2) L)).det ≠ 0 := (Matrix.isUnits_det_units t).ne_zero
  rw [Matrix.det_fin_two, ht₂, zero_mul, sub_zero] at hdet
  have ha0 : (t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 :=
    div_ne_zero (left_ne_zero_of_mul hdet) (right_ne_zero_of_mul hdet)
  have hc : algebraMap K L (Algebra.norm K
      ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0)) ≠ 1 := by
    intro h
    rw [← inv_div, ← map_one (algebraMap K L)] at h
    have h1 := (algebraMap K L).injective h
    have h2 := map_mul (Algebra.norm K) ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1)
      ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1)⁻¹
    rw [mul_inv_cancel₀ ha0, map_one, h1, mul_one] at h2
    exact hnorm h2.symm

  have hinv : (↑hAu.unit⁻¹ : AdeleRing (𝓞 L) L) * A = 1 := hAu.val_inv_mul
  have hσ : (D.act σ) x = (B * ↑hAu.unit⁻¹) * x + E * ↑hAu.unit⁻¹ := by
    linear_combination (↑hAu.unit⁻¹ : AdeleRing (𝓞 L) L) * hres - ((D.act σ) x) * hinv
  have hN : ∏ i ∈ Finset.range (Module.finrank K L), (⇑(D.act σ))^[i] (B * ↑hAu.unit⁻¹) =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L
        (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0))) := by
    rw [prod_iterate_map_mul, hnormB, mul_assoc, ← prod_iterate_map_mul, hAu.mul_val_inv,
      Finset.prod_eq_one (fun i _ => iterate_map_one (D.act σ) i), mul_one]
  have hout' : ∀ v, v ∉ S ∪ T → ∀ w : v.Extension (𝓞 L),
      ‖(B * ↑hAu.unit⁻¹).2 w.1‖ ≤ 1 ∧ ‖(E * ↑hAu.unit⁻¹).2 w.1‖ ≤ 1 := fun v hv w => by
    rw [norm_snd_mul_unit_inv L A B hAu, norm_snd_mul_unit_inv L A E hAu]
    exact ⟨(hout v hv w).1.le, (hout v hv w).2⟩
  have hT' : ∀ v ∈ T, ∀ w : v.Extension (𝓞 L),
      ‖(B * ↑hAu.unit⁻¹).2 w.1‖ ≤ Real.exp (A₀ * m v) ∧ ‖(E * ↑hAu.unit⁻¹).2 w.1‖ ≤ Real.exp (A₀ * m v) :=
    fun v hv w => by
    rw [norm_snd_mul_unit_inv L A B hAu, norm_snd_mul_unit_inv L A E hAu]
    exact ⟨le_exp_of_abs_log_le _ _ (norm_nonneg _) (hT v hv w).1,
      le_exp_of_posLog_le _ _ (norm_nonneg _) (hT v hv w).2⟩
  have hS' : ∀ v ∈ S, v ∉ T → ∀ w : v.Extension (𝓞 L),
      ‖(B * ↑hAu.unit⁻¹).2 w.1‖ ≤ Real.exp (max cS 0) ∧ ‖(E * ↑hAu.unit⁻¹).2 w.1‖ ≤ Real.exp (max cS 0) :=
    fun v hv hv' w => by
    rw [norm_snd_mul_unit_inv L A B hAu, norm_snd_mul_unit_inv L A E hAu]
    exact ⟨le_exp_of_abs_log_le _ _ (norm_nonneg _) ((hS v hv hv' w).1.trans (le_max_left _ _)),
      le_exp_of_posLog_le _ _ (norm_nonneg _) ((hS v hv hv' w).2.trans (le_max_left _ _))⟩
  have hinf' : ∀ w : InfinitePlace L,
      ‖(B * ↑hAu.unit⁻¹).1 w‖ ≤ Real.exp (max cinf 0) ∧ ‖(E * ↑hAu.unit⁻¹).1 w‖ ≤ Real.exp (max cinf 0) :=
    fun w => by
    rw [norm_fst_mul_unit_inv L A B hAu, norm_fst_mul_unit_inv L A E hAu]
    exact ⟨le_exp_of_abs_log_le _ _ (norm_nonneg _) ((hinf w).1.trans (le_max_left _ _)),
      le_exp_of_posLog_le _ _ (norm_nonneg _) ((hinf w).2.trans (le_max_left _ _))⟩
  have key := abs_excursion_le_of_windows D σ S T (Module.finrank K L) A₀ (max cS 0) (max cinf 0) hA₀
    (le_max_right _ _) (le_max_right _ _) m hm x (B * ↑hAu.unit⁻¹) (E * ↑hAu.unit⁻¹)
    (algebraMap K L (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0)))
    hc hσ hper hN hout' hT' hS' hinf'
  unfold excursionConstant
  exact key

end Resolvent

section Measure

open scoped ENNReal TensorProduct.RightActions in

theorem one_le_toReal_semiLocalHaar_doubleCoset
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    1 ≤ (AutomorphicForm.semiLocalHaar K L v
      (semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v)).toReal := by
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensorGL K L (v.adicCompletion K)
  haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L (v.adicCompletion K)
  haveI := AutomorphicForm.isHaarMeasure_semiLocalHaar K L v
  haveI : ContinuousMul (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := IsTopologicalGroup.toContinuousMul
  haveI : MeasurableMul (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := ContinuousMul.measurableMul
  have hK := AutomorphicForm.isCompact_semiLocalIntegralSet K L v
  have hfin : AutomorphicForm.semiLocalHaar K L v
      (semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v) ≠ ⊤ :=
    ((hK.mul isCompact_singleton).mul hK).measure_lt_top.ne
  have hsub : (fun h => a⁻¹ * h) ⁻¹' semiLocalIntegralSet K L v ⊆
      semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v := by
    intro x hx
    refine ⟨1 * a, Set.mul_mem_mul (AutomorphicForm.one_mem_semiLocalIntegralSet K L v) rfl, a⁻¹ * x, hx, ?_⟩
    simp
  have hone : AutomorphicForm.semiLocalHaar K L v ((fun h => a⁻¹ * h) ⁻¹' semiLocalIntegralSet K L v) = 1 := by
    rw [MeasureTheory.measure_preimage_mul, AutomorphicForm.semiLocalHaar_semiLocalIntegralSet]
  have hle : (1 : ℝ≥0∞) ≤ AutomorphicForm.semiLocalHaar K L v
      (semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v) :=
    hone ▸ MeasureTheory.measure_mono hsub
  simpa using ENNReal.toReal_mono hfin hle

end Measure

end AutomorphicForm.ExcursionAssembly

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_forall_abs_log_adelicHeight_mul_adelicHeight_adelicWeyl_le_mul_prod_pow_log_measure_of_doubleCoset_apply_ne_zero.AutomorphicForm in
open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)),
      ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℕ,
      ∀ (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v) →
      ∀ (t : GL (Fin 2) L), (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
        Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
      ∀ (y : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
        φ (y⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ≠ 0 →
        |(-Real.log (NumberField.AdelicHeight.adelicHeight L y)
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * y)))| ≤
        C * ∏ v ∈ T,
          ((1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ A) := by
  classical
  intro T ws

  obtain ⟨A₀, hA₀, cS, cinf, hwin⟩ :=
    AutomorphicForm.exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero
      K L D σ hgen S φa φS T ws
  refine ⟨AutomorphicForm.ExcursionAssembly.excursionConstant K L S T A₀ (max cS 0) (max cinf 0),
    AutomorphicForm.ExcursionAssembly.excursionConstant_nonneg S T A₀ (max cS 0) (max cinf 0) hA₀
      (le_max_right _ _) (le_max_right _ _), 1, ?_⟩
  intro ρ φ φf hfact t ht10 ht01 hnorm y z hφ

  obtain ⟨b, k, hb, hk1, hk2, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq L y
  have hk : k ∈ AutomorphicForm.adelicMaximalCompact L :=
    AutomorphicForm.mem_adelicMaximalCompact_iff.mpr ⟨hk1, hk2⟩

  rw [NumberField.AdelicHeight.neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_eq_unipotentGL2_of_mem_adelicBorel
      L b k hb hk,
    NumberField.AdelicHeight.neg_log_adelicHeight_unipotentGL2_sub_log_adelicHeight_adelicWeyl_mul_unipotentGL2_eq]

  obtain ⟨⟨hAu, -⟩, hres, hnormB, hper⟩ :=
    AutomorphicForm.isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal
      K L D σ hgen t ht10 ht01 b hb z _ _ _ rfl rfl rfl

  have hw := hwin ρ φ φf hfact t ht10 ht01 b hb k hk z hφ _ _ _ rfl rfl rfl

  have hm : ∀ v ∈ T, (1 : ℝ) ≤ (fun v : HeightOneSpectrum (𝓞 K) => 1 + Real.log (AutomorphicForm.semiLocalHaar K L v
      (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
        semiLocalIntegralSet K L v)).toReal) v := fun v _ => by
    have h := Real.log_nonneg
      (AutomorphicForm.ExcursionAssembly.one_le_toReal_semiLocalHaar_doubleCoset K L v
        (semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v))))
    linarith

  have hmain := AutomorphicForm.ExcursionAssembly.abs_excursion_le_of_resolvent D σ S T A₀ cS cinf hA₀ _ hm
    t ht01 hnorm _ _ _ _ hAu hres hnormB hper hw
  simpa only [pow_one] using hmain

end S_AutomorphicForm_exists_forall_abs_log_adelicHeight_mul_adelicHeight_adelicWeyl_le_mul_prod_pow_log_measure_of_doubleCoset_apply_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_abs_log_adelicHeight_mul_adelicHeight_adelicWeyl_le_mul_prod_pow_log_measure_of_doubleCoset_apply_ne_zero (solution)

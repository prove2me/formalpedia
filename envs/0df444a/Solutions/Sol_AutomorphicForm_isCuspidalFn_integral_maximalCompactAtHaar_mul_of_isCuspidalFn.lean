-- Prove2me | solution 1 for AutomorphicForm.isCuspidalFn_integral_maximalCompactAtHaar_mul_of_isCuspidalFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7682360d-383e-565b-b714-ec937f7481c1

import Mathlib
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isCuspidalFn_integral_maximalCompactAtHaar_mul_of_isCuspidalFn

set_option autoImplicit false

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 160000

noncomputable section

namespace Ws23
namespace CuspAvg

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.TateGlobal IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

variable {K : Type} [Field K] [NumberField K]

section Riemann

variable (K)

abbrev Kc : Type := ↥(maximalCompactAt K ∅)

abbrev μK : Measure (Kc K) := maximalCompactAtHaar K ∅

def coords (k : Kc K) : ∀ w : InfinitePlace K, (Fin 2 → Fin 2 → w.Completion) × (Fin 2 → Fin 2 → w.Completion) :=
  fun w => (fun i j => ((archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K)) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) i j,
    fun i j => (((archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K)))⁻¹ : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) i j)

variable {K}

theorem continuous_coords : Continuous (coords K) := by
  refine continuous_pi fun w => Continuous.prodMk ?_ ?_
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact ((Units.continuous_val.comp ((continuous_archComponent K w).comp ((continuous_glArch (𝓞 K) K).comp
      continuous_subtype_val))).matrix_elem i j)
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact ((Units.continuous_val.comp (continuous_inv.comp ((continuous_archComponent K w).comp
      ((continuous_glArch (𝓞 K) K).comp continuous_subtype_val)))).matrix_elem i j)

theorem eq_of_glArch_eq_of_glFin_eq {a b : AdelicGL2 (𝓞 K) K}
    (hA : glArch (𝓞 K) K a = glArch (𝓞 K) K b) (hF : glFin (𝓞 K) K a = glFin (𝓞 K) K b) : a = b := by
  apply Units.ext
  ext i j
  refine Prod.ext ?_ ?_
  · have := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing K) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) hA
    simpa only [glArch_apply] using this
  · have := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) hF
    simpa only [glFin_apply] using this

theorem glFin_eq_one_of_mem {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ maximalCompactAt K ∅) : glFin (𝓞 K) K k = 1 := by
  have h := (mem_maximalCompactAt_iff.1 hk).2
  apply Units.ext
  ext i j v
  have hv := congrArg (fun m : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) =>
    (m : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)) i j) (h v (Finset.notMem_empty v))
  simp only [finComponent_apply] at hv
  rw [hv, Units.val_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem injective_coords : Function.Injective (coords K) := by
  intro a b h
  apply Subtype.ext
  refine eq_of_glArch_eq_of_glFin_eq ?_ (by rw [glFin_eq_one_of_mem a.2, glFin_eq_one_of_mem b.2])
  apply Units.ext
  ext i j
  funext w
  have hw := congrArg (fun c => (c w).1 i j) h
  simpa only [coords, archComponent_apply] using hw

theorem isClosedEmbedding_coords : Topology.IsClosedEmbedding (coords K) :=
  continuous_coords.isClosedEmbedding injective_coords

@[reducible] def metricKc : MetricSpace (Kc K) :=
  (MetricSpace.induced (coords K) injective_coords inferInstance).replaceTopology
    isClosedEmbedding_coords.isInducing.eq_induced

theorem exists_partition (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (E : Fin N → Set (Kc K)) (c : Fin N → Kc K),
      (∀ i, MeasurableSet (E i)) ∧ Pairwise (Function.onFun Disjoint E) ∧ (⋃ i, E i) = Set.univ ∧
      ∀ i, ∀ k ∈ E i, @dist (Kc K) (metricKc (K := K)).toDist k (c i) < ε := by
  letI : MetricSpace (Kc K) := metricKc
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact (isCompact_univ : IsCompact (Set.univ : Set (Kc K))) hε
  obtain ⟨N, e⟩ : ∃ N : ℕ, Nonempty (Fin N ≃ t) := ⟨htf.toFinset.card, ⟨(htf.toFinset.equivFin.symm.trans (Equiv.subtypeEquivRight
    (fun x => by simp))) ⟩⟩
  obtain ⟨e⟩ := e
  let B : ℕ → Set (Kc K) := fun n => if h : n < N then Metric.ball ((e ⟨n, h⟩ : t) : Kc K) ε else ∅
  refine ⟨N, fun i => disjointed B i, fun i => ((e i : t) : Kc K), fun i => ?_, ?_, ?_, ?_⟩
  · refine MeasurableSet.disjointed (fun n => ?_) i
    by_cases h : n < N
    · simp only [B, dif_pos h]; exact Metric.isOpen_ball.measurableSet
    · simp only [B, dif_neg h]; exact MeasurableSet.empty
  · intro i j hij
    exact disjoint_disjointed B (Fin.val_injective.ne hij)
  · apply Set.eq_univ_of_forall
    intro k
    have hk := hcov (Set.mem_univ k)
    simp only [Set.mem_iUnion] at hk
    obtain ⟨x, hx, hkx⟩ := hk
    obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
    have hkB : k ∈ B i := by
      simp only [B, dif_pos i.2, hi]
      exact hkx
    have hkU : k ∈ ⋃ n, B n := Set.mem_iUnion.2 ⟨i, hkB⟩
    rw [← iUnion_disjointed] at hkU
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hkU
    have hnN : n < N := by
      by_contra hnN
      have : disjointed B n ⊆ B n := disjointed_subset B n
      have := this hn
      simp only [B, dif_neg hnN] at this
      exact this
    exact Set.mem_iUnion.2 ⟨⟨n, hnN⟩, hn⟩
  · intro i k hk
    have hk' : k ∈ B i := disjointed_subset B i hk
    simp only [B, dif_pos i.2] at hk'
    exact hk'

def partN (m : ℕ) : ℕ := (exists_partition (K := K) (1 / ((m : ℝ) + 1)) (by positivity)).choose
def partE (m : ℕ) : Fin (partN (K := K) m) → Set (Kc K) :=
  (exists_partition (K := K) (1 / ((m : ℝ) + 1)) (by positivity)).choose_spec.choose
def partC (m : ℕ) : Fin (partN (K := K) m) → Kc K :=
  (exists_partition (K := K) (1 / ((m : ℝ) + 1)) (by positivity)).choose_spec.choose_spec.choose
theorem partE_spec (m : ℕ) :
    (∀ i, MeasurableSet (partE (K := K) m i)) ∧ Pairwise (Function.onFun Disjoint (partE (K := K) m)) ∧
      (⋃ i, partE (K := K) m i) = Set.univ ∧
      ∀ i, ∀ k ∈ partE (K := K) m i, @dist (Kc K) (metricKc (K := K)).toDist k (partC m i) < 1 / ((m : ℝ) + 1) :=
  (exists_partition (K := K) (1 / ((m : ℝ) + 1)) (by positivity)).choose_spec.choose_spec.choose_spec

def riemannSum (m : ℕ) (h : Kc K → ℂ) : ℂ := ∑ i, ((μK K (partE m i)).toReal : ℂ) * h (partC m i)

theorem tendsto_riemannSum (h : Kc K → ℂ) (hh : Continuous h) :
    Filter.Tendsto (fun m => riemannSum m h) Filter.atTop (nhds (∫ k, h k ∂(μK K))) := by
  letI : MetricSpace (Kc K) := metricKc
  rw [Metric.tendsto_atTop]
  intro η hη

  have huc : UniformContinuous h := CompactSpace.uniformContinuous_of_continuous hh
  obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuous_iff.1 huc (η / 2) (half_pos hη)
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
  refine ⟨M, fun m hm => ?_⟩
  have hmesh : 1 / ((m : ℝ) + 1) < δ := by
    have hMpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ hMpos]
    have : 1 / δ < (m : ℝ) + 1 := hM.trans_le (by exact_mod_cast Nat.le_succ_of_le hm)
    rw [div_lt_iff₀ hδ] at this
    linarith
  obtain ⟨hmeas, hdisj, hcov, hsmall⟩ := partE_spec (K := K) m
  have hint : Integrable h (μK K) := hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace h) |>.mono_measure le_rfl

  have hsplit : ∫ k, h k ∂(μK K) = ∑ i, ∫ k in partE m i, h k ∂(μK K) := by
    rw [← MeasureTheory.setIntegral_univ, ← hcov, MeasureTheory.integral_iUnion hmeas hdisj hint.integrableOn, tsum_fintype]

  have hconst : ∀ i, ((μK K (partE m i)).toReal : ℂ) * h (partC m i) = ∫ k in partE m i, h (partC m i) ∂(μK K) := by
    intro i
    rw [MeasureTheory.setIntegral_const, Complex.real_smul]
    rfl
  rw [dist_eq_norm, riemannSum, hsplit, ← Finset.sum_sub_distrib]
  calc ‖∑ i, (((μK K (partE m i)).toReal : ℂ) * h (partC m i) - ∫ k in partE m i, h k ∂(μK K))‖
      ≤ ∑ i, ‖((μK K (partE m i)).toReal : ℂ) * h (partC m i) - ∫ k in partE m i, h k ∂(μK K)‖ := norm_sum_le _ _
    _ ≤ ∑ i, (η / 2) * (μK K (partE m i)).toReal := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hconst, ← MeasureTheory.integral_sub (MeasureTheory.integrable_const _) hint.integrableOn]
        have hle : ∀ k ∈ partE m i, ‖h (partC m i) - h k‖ ≤ η / 2 := fun k hk => by
          rw [← dist_eq_norm]
          exact (hδc (by rw [dist_comm]; exact (hsmall i k hk).trans hmesh)).le
        exact MeasureTheory.norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hle
    _ = (η / 2) * ∑ i, (μK K (partE m i)).toReal := by rw [Finset.mul_sum]
    _ = (η / 2) * 1 := by
        congr 1
        have hU : μK K Set.univ = ∑ i, μK K (partE m i) := by
          rw [← hcov, ← measure_biUnion_finset (fun i _ j _ hij => hdisj hij) (fun i _ => hmeas i)]
          simp
        rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top _ _), ← hU, measure_univ, ENNReal.toReal_one]
    _ < η := by linarith

end Riemann

section Sums

def avgSum (κ : Kc K → ℝ) (f : AdelicGL2 (𝓞 K) K → ℂ) (m : ℕ) (x : AdelicGL2 (𝓞 K) K) : ℂ :=
  riemannSum m fun k => (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K))

theorem avgSum_eq (κ : Kc K → ℝ) (f : AdelicGL2 (𝓞 K) K → ℂ) (m : ℕ) (x : AdelicGL2 (𝓞 K) K) :
    avgSum κ f m x = ∑ i, (((μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i) : ℝ) : ℂ) * f (x * ((partC (K := K) m i : Kc K) : AdelicGL2 (𝓞 K) K)) := by
  simp only [avgSum, riemannSum, Complex.ofReal_mul, mul_assoc]

theorem continuous_avgSum (κ : Kc K → ℝ) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) (m : ℕ) :
    Continuous (avgSum κ f m) := by
  have e : avgSum κ f m = fun x => ∑ i, (((μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i) : ℝ) : ℂ) *
      f (x * ((partC (K := K) m i : Kc K) : AdelicGL2 (𝓞 K) K)) := funext (avgSum_eq κ f m)
  rw [e]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (hf.comp (continuous_mul_const _))

theorem tendsto_avgSum {κ : Kc K → ℝ} (hκc : Continuous κ) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f)
    (x : AdelicGL2 (𝓞 K) K) :
    Filter.Tendsto (fun m => avgSum κ f m x) Filter.atTop
      (nhds (∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(μK K))) :=
  tendsto_riemannSum _ ((Complex.continuous_ofReal.comp hκc).mul (hf.comp (continuous_const_mul x |>.comp continuous_subtype_val)))

theorem tendsto_sum_weights {κ : Kc K → ℝ} (hκc : Continuous κ) (hκ1 : ∫ k, κ k ∂(μK K) = 1) :
    Filter.Tendsto (fun m => ∑ i, (μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i)) Filter.atTop (nhds 1) := by
  have h : Filter.Tendsto (fun m => riemannSum m fun k => (κ k : ℂ)) Filter.atTop (nhds (∫ k, (κ k : ℂ) ∂(μK K))) :=
    tendsto_riemannSum (K := K) (fun k => (κ k : ℂ)) (Complex.continuous_ofReal.comp hκc)
  have hint : Integrable (fun k => (κ k : ℂ)) (μK K) :=
    (Complex.continuous_ofReal.comp hκc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hre : (∫ k, (κ k : ℂ) ∂(μK K)).re = 1 := by
    rw [← hκ1]
    have := Complex.reCLM.integral_comp_comm hint
    simp only [Complex.reCLM_apply, Complex.ofReal_re] at this
    exact this.symm
  have h' := (Complex.continuous_re.tendsto _).comp h
  rw [hre] at h'
  refine h'.congr fun m => ?_
  simp only [Function.comp_apply, riemannSum, Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem weights_nonneg {κ : Kc K → ℝ} (hκ0 : ∀ k, 0 ≤ κ k) (m : ℕ) (i : Fin (partN (K := K) m)) :
    0 ≤ (μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i) :=
  mul_nonneg ENNReal.toReal_nonneg (hκ0 _)

end Sums

section Cusp

theorem continuous_unipotentGL2' : Continuous fun q : AdeleRing (𝓞 K) K => (unipotentGL2 q : AdelicGL2 (𝓞 K) K) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun q : AdeleRing (𝓞 K) K => (!![1, q; 0, 1] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_id
  · show Continuous fun q : AdeleRing (𝓞 K) K => (!![1, -q; 0, 1] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_id | exact continuous_neg

theorem main
    (ν : @Measure (AdeleRing (𝓞 K) K) (adeleBorel (𝓞 K) K)) (hν : ν Set.univ ≠ ⊤)
    (B : Set (AdeleRing (𝓞 K) K)) (hB : IsCompact B) (hνB : ν Bᶜ = 0)
    (κ : Kc K → ℝ) (hκc : Continuous κ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f)
    (hfc : @IsCuspidalFn (AdeleRing (𝓞 K) K) (adeleBorel (𝓞 K) K) (AdelicGL2 (𝓞 K) K) _ ν
      (fun q => unipotentGL2 q) f) :
    @IsCuspidalFn (AdeleRing (𝓞 K) K) (adeleBorel (𝓞 K) K) (AdelicGL2 (𝓞 K) K) _ ν
      (fun q => unipotentGL2 q) (fun x => ∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(μK K)) := by
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := ⟨rfl⟩
  haveI : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.2 hν⟩
  intro g
  have hfc' : ∀ x : AdelicGL2 (𝓞 K) K, ∫ q, f (unipotentGL2 q * x) ∂ν = 0 := fun x => hfc x
  show ∫ q, (∫ k, (κ k : ℂ) * f (unipotentGL2 q * g * (k : AdelicGL2 (𝓞 K) K)) ∂(μK K)) ∂ν = 0

  have hνB' : ν.restrict B = ν := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; exact hνB)
  have hnu : Continuous fun q : AdeleRing (𝓞 K) K => (unipotentGL2 q : AdelicGL2 (𝓞 K) K) := continuous_unipotentGL2'

  have hInt : ∀ (F : AdeleRing (𝓞 K) K → ℂ), Continuous F → Integrable F ν := by
    intro F hF
    rw [← hνB']
    exact hF.continuousOn.integrableOn_compact hB

  obtain ⟨κmax, hκmax⟩ : ∃ C, ∀ k, ‖κ k‖ ≤ C :=
    ⟨_, fun k => le_csSup ((isCompact_range hκc.norm).bddAbove) (Set.mem_range_self k)⟩
  have hcontF : Continuous fun p : AdeleRing (𝓞 K) K × Kc K => f (unipotentGL2 p.1 * g * (p.2 : AdelicGL2 (𝓞 K) K)) :=
    hf.comp (((hnu.comp continuous_fst).mul continuous_const).mul (continuous_subtype_val.comp continuous_snd))
  obtain ⟨M, hM⟩ := (hB.prod (isCompact_univ : IsCompact (Set.univ : Set (Kc K)))).exists_bound_of_continuousOn
    hcontF.continuousOn

  have hH0 : ∀ m, ∫ q, avgSum κ f m (unipotentGL2 q * g) ∂ν = 0 := by
    intro m
    simp_rw [avgSum_eq]
    rw [integral_finset_sum Finset.univ]
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [integral_const_mul]
      have h := hfc' (g * ((partC (K := K) m i : Kc K) : AdelicGL2 (𝓞 K) K))
      simp only [← mul_assoc] at h
      rw [h, mul_zero]
    · intro i _
      exact (hInt (fun q => f (unipotentGL2 q * g * ((partC (K := K) m i : Kc K) : AdelicGL2 (𝓞 K) K)))
        (hf.comp ((hnu.mul continuous_const).mul continuous_const))).const_mul _

  have hmeasH : ∀ m, AEStronglyMeasurable (fun q => avgSum κ f m (unipotentGL2 q * g)) ν := fun m =>
    ((continuous_avgSum κ hf m).comp (hnu.mul continuous_const)).aestronglyMeasurable
  have hsum1 : ∀ m, ∑ i, (μK K (partE (K := K) m i)).toReal = 1 := by
    intro m
    obtain ⟨hmeas, hdisj, hcov, -⟩ := partE_spec (K := K) m
    have hU : μK K Set.univ = ∑ i, μK K (partE m i) := by
      rw [← hcov, ← measure_biUnion_finset (fun i _ j _ hij => hdisj hij) (fun i _ => hmeas i)]
      simp
    rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top _ _), ← hU, measure_univ, ENNReal.toReal_one]
  have hbound : ∀ m, ∀ᵐ q ∂ν, ‖avgSum κ f m (unipotentGL2 q * g)‖ ≤ κmax * M := by
    intro m
    have hB' : ∀ᵐ q ∂ν, q ∈ B := by rw [ae_iff]; exact hνB
    filter_upwards [hB'] with q hq
    rw [avgSum_eq]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖((((μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i) : ℝ)) : ℂ) *
            f (unipotentGL2 q * g * ((partC (K := K) m i : Kc K) : AdelicGL2 (𝓞 K) K))‖
        ≤ ∑ i, (μK K (partE (K := K) m i)).toReal * (κmax * M) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          exact mul_le_mul ((Real.norm_eq_abs _).symm.le.trans (hκmax _)) (hM ⟨q, _⟩ ⟨hq, Set.mem_univ _⟩)
            (norm_nonneg _) ((norm_nonneg _).trans (hκmax 1))
      _ = κmax * M := by rw [← Finset.sum_mul, hsum1, one_mul]
  have hlim : ∀ᵐ q ∂ν, Filter.Tendsto (fun m => avgSum κ f m (unipotentGL2 q * g)) Filter.atTop
      (nhds (∫ k, (κ k : ℂ) * f (unipotentGL2 q * g * (k : AdelicGL2 (𝓞 K) K)) ∂(μK K))) :=
    Filter.Eventually.of_forall fun q => tendsto_avgSum hκc hf _
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ => κmax * M) hmeasH (integrable_const _) hbound hlim
  simp_rw [hH0] at hDCT
  exact (tendsto_nhds_unique tendsto_const_nhds hDCT).symm

end Cusp

end Ws23.CuspAvg

end

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (K : Type) [Field K] [NumberField K]
    (ν : @Measure (AdeleRing (𝓞 K) K) (adeleBorel (𝓞 K) K)) (hν : ν Set.univ ≠ ⊤)
    (B : Set (AdeleRing (𝓞 K) K)) (hB : IsCompact B) (hνB : ν Bᶜ = 0)
    (κ : ↥(maximalCompactAt K ∅) → ℝ) (hκc : Continuous κ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f)
    (hfc : @IsCuspidalFn (AdeleRing (𝓞 K) K) (adeleBorel (𝓞 K) K) (AdelicGL2 (𝓞 K) K) _ ν
      (fun q => unipotentGL2 q) f) :
    @IsCuspidalFn (AdeleRing (𝓞 K) K) (adeleBorel (𝓞 K) K) (AdelicGL2 (𝓞 K) K) _ ν
      (fun q => unipotentGL2 q) (fun x => ∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactAtHaar K ∅)) :=
  Ws23.CuspAvg.main ν hν B hB hνB κ hκc f hf hfc

end S_AutomorphicForm_isCuspidalFn_integral_maximalCompactAtHaar_mul_of_isCuspidalFn
end P2MW
export P2MW.S_AutomorphicForm_isCuspidalFn_integral_maximalCompactAtHaar_mul_of_isCuspidalFn (solution)

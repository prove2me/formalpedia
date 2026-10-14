-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0199_parallel1
-- name    : PNT_ZeroFree_433_0199_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:24:54.375054+00:00
-- url     : https://prove2.me/theorems/a798f922-cded-4754-9173-967c2280ee65
-- title:
--   Zero-free region foundations: CubicSieve.ClosedRecursion [0199_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.ClosedRecursion
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ClosedRecursion.lean#L486-L637

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0147_parallel1
import Definitions.Def_PNT_ZeroFree_433_0151_parallel2
import Definitions.Def_PNT_ZeroFree_433_0153_parallel1
import Definitions.Def_PNT_ZeroFree_433_0155_parallel1
import Definitions.Def_PNT_ZeroFree_433_0182_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ClosedRecursion.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff


open scoped BigOperators Classical
namespace CompletedGauss
open ActualEisensteinCubic UniqueFactorizationMonoid

theorem nonresidual_count_eq_on_fiber (I J Q P : Ideal ActualEisensteinCubic.O)
    (hI : I≠0) (hP : Prime P)
    (hA : rowPowerfulPart I=rowPowerfulPart J)
    (hT : rowMaskPart I Q=rowMaskPart J Q)
    (hpool : P∣I*Q) (hr : ¬P∣rowResidualPart I Q) :
    (normalizedFactors I).count P=(normalizedFactors J).count P := by
  have ha := congrArg (fun A : Ideal ActualEisensteinCubic.O=>(normalizedFactors A).count P) hA
  simp only [normalizedFactors_rowPowerfulPart,Multiset.count_filter] at ha
  have ht := congrArg (fun A : Ideal ActualEisensteinCubic.O=>(normalizedFactors A).count P) hT
  simp only [rowMaskPart,normalizedFactors_squarefreeMaskPart,
    normalizedFactors_rowSimplePart,Multiset.count_filter] at ht
  have hr0 : (normalizedFactors (rowResidualPart I Q)).count P=0 := by
    apply Multiset.count_eq_zero.mpr
    intro hm
    exact hr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart I) Q)).mp hm).2
  simp only [rowResidualPart,normalizedFactors_squarefreeResidualPart,
    normalizedFactors_rowSimplePart,Multiset.count_filter] at hr0
  by_cases hpq : P∣Q
  · simp only [hpq,ite_true] at ht
    by_cases hi : 2≤(normalizedFactors I).count P <;>
      by_cases hj : 2≤(normalizedFactors J).count P <;> simp only [hi,hj,ite_true,ite_false,not_true_eq_false,not_false_eq_true] at ha ht <;> omega
  · have hpi : P∣I := (hP.dvd_mul.mp hpool).resolve_right hpq
    have hci : 0<(normalizedFactors I).count P :=
      Multiset.count_pos.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨hP,hpi⟩)
    simp only [hpq,not_false_eq_true,ite_true] at hr0
    by_cases hi : 2≤(normalizedFactors I).count P <;>
      by_cases hj : 2≤(normalizedFactors J).count P <;> simp only [hi,hj,ite_true,ite_false,not_true_eq_false,not_false_eq_true] at ha hr0 <;> omega

theorem nonresidual_prime_transport (I J F Q P : Ideal ActualEisensteinCubic.O)
    (hI : I≠0) (hJ : J≠0) (hP : Prime P)
    (hA : rowPowerfulPart I=rowPowerfulPart J)
    (hT : rowMaskPart I Q=rowMaskPart J Q)
    (hpool : P∣I*Q) (hr : ¬P∣rowResidualPart I Q) :
    P∣J*Q ∧ ¬P∣rowResidualPart J Q ∧ completedLocalExponent I F P=completedLocalExponent J F P := by
  have hc := nonresidual_count_eq_on_fiber I J Q P hI hP hA hT hpool hr
  have hpoolJ : P∣J*Q := by
    rcases hP.dvd_mul.mp hpool with hi|hq
    · have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨hP,hi⟩
      have hcj : 0<(normalizedFactors J).count P := hc ▸ Multiset.count_pos.mpr hm
      exact dvd_mul_of_dvd_left ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hJ).mp (Multiset.count_pos.mp hcj)).2 Q
    · exact dvd_mul_of_dvd_right hq J
  have hrc : (normalizedFactors (rowResidualPart I Q)).count P=
      (normalizedFactors (rowResidualPart J Q)).count P := by
    simp only [rowResidualPart,normalizedFactors_squarefreeResidualPart,
      normalizedFactors_rowSimplePart,Multiset.count_filter,hc]
  refine ⟨hpoolJ,?_,?_⟩
  · intro hd
    have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart J) Q)).mpr ⟨hP,hd⟩
    have hp : 0<(normalizedFactors (rowResidualPart I Q)).count P := hrc.symm ▸ Multiset.count_pos.mpr hm
    exact hr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart I) Q)).mp
      (Multiset.count_pos.mp hp)).2
  · simp only [completedLocalExponent,hc]


end CompletedGauss

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

omit [CompleteSpace E] in
lemma compact_estimate_prod_antilipschitz (T : E→L[ℂ]F) (K : E→L[ℂ]G) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) :
    ∃D : NNReal,AntilipschitzWith D (T.prod K) := by
  let R := max A 0+max B 0
  have hR : 0≤R := add_nonneg (le_max_right _ _) (le_max_right _ _)
  refine ⟨⟨Real.sqrt R,Real.sqrt_nonneg _⟩,(T.prod K).antilipschitz_of_bound (fun u => ?_)⟩
  have hT : ‖T u‖^2≤‖(T.prod K) u‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_fst_le (T u,K u))
  have hK : ‖K u‖^2≤‖(T.prod K) u‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_snd_le (T u,K u))
  have hh : ‖u‖^2≤R*‖(T.prod K) u‖^2 := calc
    _ ≤A*‖T u‖^2+B*‖K u‖^2 := hest u
    _ ≤max A 0*‖T u‖^2+max B 0*‖K u‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    _ ≤max A 0*‖(T.prod K) u‖^2+max B 0*‖(T.prod K) u‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hT (le_max_right _ _))
        (mul_le_mul_of_nonneg_left hK (le_max_right _ _))
    _ = _ := by dsimp only [R]; ring
  change ‖u‖≤Real.sqrt R*‖(T.prod K) u‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow,Real.sq_sqrt hR] using hh

lemma finiteDimensional_ker_of_compact_estimate (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) :
    FiniteDimensional ℂ T.ker := by
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  have hc : IsCompactOperator (K.comp T.ker.subtypeL) := hK.comp_clm T.ker.subtypeL
  have hid : IsCompactOperator (ContinuousLinearMap.id ℂ T.ker) := by
    apply compact_of_norm_le_compact _ _ hc
    refine ⟨Real.sqrt (max B 0),fun u => ?_⟩
    have ht : T (u:E)=0 := u.2
    have hh := hest (u:E)
    rw [ht,norm_zero,zero_pow (by decide : 2≠0),mul_zero,zero_add] at hh
    have hh' : ‖u‖^2≤max B 0*‖K (u:E)‖^2 :=
      hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    change ‖u‖≤Real.sqrt (max B 0)*‖K (u:E)‖
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow,Real.sq_sqrt (le_max_right B 0)] using hh'
  exact FiniteDimensional.of_isCompactOperator_id hid

lemma antilipschitz_of_injective_compact_estimate (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) (hT : Function.Injective T) :
    ∃D : NNReal,AntilipschitzWith D T := by
  by_contra hanti
  have hex (ε : ℝ) (hε : 0<ε) : ∃u : E,‖u‖=1 ∧ ‖T u‖<ε := by
    by_contra! hn
    apply hanti
    refine ⟨⟨ε⁻¹,inv_nonneg.mpr hε.le⟩,antilipschitz_of_bound_of_norm_one T (fun u hu => ?_)⟩
    change 1≤ε⁻¹*‖T u‖
    have hh := mul_le_mul_of_nonneg_left (hn u hu) (inv_nonneg.mpr hε.le)
    simpa only [inv_mul_cancel₀ hε.ne'] using hh
  obtain ⟨eps,hepsAnti,hepsPos,heps⟩ := exists_seq_strictAnti_tendsto (0:ℝ)
  choose u hunorm huT using fun n : ℕ => hex (eps n) (hepsPos n)
  have huTlim : Tendsto (fun n => T (u n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (huT n).le) heps
  obtain ⟨S,hS,hsub⟩ := hK.image_closedBall_subset_compact 1
  obtain ⟨k,hk,seq,hseq,hklim⟩ := hS.tendsto_subseq
    (fun n => hsub ⟨u n,by simp only [Metric.mem_closedBall,dist_zero_right,hunorm,le_refl],rfl⟩)
  let P := T.prod K
  obtain ⟨D,hD⟩ := compact_estimate_prod_antilipschitz T K A B hest
  have hlim : Tendsto (fun n => P (u (seq n))) atTop (𝓝 (0,k)) :=
    (huTlim.comp hseq.tendsto_atTop).prodMk_nhds hklim
  have hmem : (0,k)∈Set.range P :=
    (hD.isClosed_range P.uniformContinuous).mem_of_tendsto hlim
      (Eventually.of_forall (fun n => ⟨u (seq n),rfl⟩))
  obtain ⟨v,hv⟩ := hmem
  have hvlim : Tendsto (fun n => u (seq n)) atTop (𝓝 v) := by
    apply (hD.isInducing P.continuous).tendsto_nhds_iff.mpr
    change Tendsto (fun n => P (u (seq n))) atTop (𝓝 (P v))
    rw [hv]
    exact hlim
  have hvzero : v=0 := hT (by
    have hh := congrArg Prod.fst hv
    change T v=0 at hh
    simpa only [map_zero] using hh)
  have hnorm : ‖v‖=1 := tendsto_nhds_unique hvlim.norm (by simpa only [hunorm] using tendsto_const_nhds)
  rw [hvzero,norm_zero] at hnorm
  norm_num at hnorm

end CubicEisenstein

end

end OAI

end



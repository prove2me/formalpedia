-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0123_parallel2
-- name    : PNT_ZeroFree_433_0123_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:30:37.655388+00:00
-- url     : https://prove2.me/theorems/6be22e5a-732f-4668-8045-14ec24312d32
-- title:
--   Zero-free region foundations: QuadraticSieve.HighKernelGeometry [0123_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.HighKernelGeometry
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/HighKernelGeometry.lean#L77-L644

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0058
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0105
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0113
import Definitions.Def_PNT_ZeroFree_433_0114
import Definitions.Def_PNT_ZeroFree_433_0123_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148
import Definitions.Def_PNT_ZeroFree_433_0173_parallel1
import Definitions.Def_PNT_ZeroFree_433_0241
import Definitions.Def_PNT_ZeroFree_433_0242_parallel2
import Definitions.Def_PNT_ZeroFree_433_0260_parallel2
import Definitions.Def_PNT_ZeroFree_433_0265_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/HighKernelGeometry.lean
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic

theorem finite_inverse_norm_square_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I ∈ S, I ≠ 0)
    (hH : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (∑ I ∈ S, 1/(Ideal.absNorm I : ℝ)^2) ≤ 1024 := by
  have hpos (I : Ideal O) (hI : I ∈ S) : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hbin (j : Fin (columnDyadicLength H+1)) :
      (∑ I ∈ divisorDyadicBin S H j, 1/(Ideal.absNorm I : ℝ)^2) ≤
        512 * (1/(2:ℝ))^j.val := by
    have hp : 0 < (2:ℝ)^j.val := by positivity
    have hone : 1 ≤ (2:ℝ)^j.val := one_le_pow₀ (by norm_num)
    have hcount : ((divisorDyadicBin S H j).card : ℝ) ≤ 128 * (2:ℝ)^j.val := by
      apply DescentFiberCost.finite_ideal_count_real _ _ hone
      · intro I hI
        exact hS I (Finset.mem_filter.mp hI).1
      · intro I hI
        obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
        have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).2
        simpa only [hj] using hb
    have hterm (I : Ideal O) (hI : I ∈ divisorDyadicBin S H j) :
        1/(Ideal.absNorm I : ℝ)^2 ≤ 4/((2:ℝ)^j.val)^2 := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).1
      rw [hj] at hb
      have hni : 0 < (Ideal.absNorm I : ℝ) := lt_of_lt_of_le (by norm_num) (hpos I hIS)
      apply (div_le_div_iff₀ (sq_pos_of_pos hni) (sq_pos_of_pos hp)).mpr
      nlinarith
    calc
      _ ≤ ∑ _I ∈ divisorDyadicBin S H j, 4/((2:ℝ)^j.val)^2 :=
        Finset.sum_le_sum hterm
      _ = ((divisorDyadicBin S H j).card : ℝ) * (4/((2:ℝ)^j.val)^2) := by simp
      _ ≤ (128 * (2:ℝ)^j.val) * (4/((2:ℝ)^j.val)^2) := by gcongr
      _ = 512 * (1/(2:ℝ))^j.val := by
        rw [div_pow,one_pow]
        field_simp
        ; ring
  rw [sum_divisorDyadicBins S H]
  calc
    _ ≤ ∑ j : Fin (columnDyadicLength H+1), 512 * (1/(2:ℝ))^j.val :=
      Finset.sum_le_sum (fun j _ => hbin j)
    _ = 512 * ∑ j ∈ Finset.range (columnDyadicLength H+1), (1/(2:ℝ))^j := by
      rw [← Finset.mul_sum,Fin.sum_univ_eq_sum_range]
    _ ≤ 512 * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by norm_num)
    _ = 1024 := by norm_num


end CanonicalQuadraticSieve


open Filter MeasureTheory
open scoped BigOperators Classical Topology


open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O


lemma integral_height_action_matrix (M : SL(2,O)) (g : SL(2,ℂ)) :
    hyperbolicHeight (integralComplexMatrix M • (QuotientGroup.mk g : HyperbolicSpace))=
      (integralRowEnergy g (integralBottomRow M))⁻¹ := by
  change (rowEnergy (complexBottomRow (integralComplexMatrix M*g)))⁻¹=_
  rw [complexBottomRow_mul]
  rfl

lemma integralRowEnergy_bottom_pos (g : SL(2,ℂ)) (M : SL(2,O)) :
    0 < integralRowEnergy g (integralBottomRow M) := by
  have h := hyperbolicHeight_pos (integralComplexMatrix M • (QuotientGroup.mk g : HyperbolicSpace))
  rw [integral_height_action_matrix,inv_pos] at h
  exact h

theorem exists_maximal_integral_height (w : HyperbolicSpace) :
    ∃N : SL(2,O), ∀M : SL(2,O),
      hyperbolicHeight (integralComplexMatrix M • w)≤hyperbolicHeight (integralComplexMatrix N • w) := by
  induction w using Quotient.inductionOn with
  | _ g =>
    let P : Set (Fin 2 → O) := Set.range integralBottomRow
    let C := integralRowEnergy g (integralBottomRow 1)
    let S : Set (Fin 2 → O) := {v | integralRowEnergy g v≤C} ∩ P
    have hS : Set.Finite S := (integralRowEnergy_sublevel_finite g C).inter_of_left P
    have hSne : S.Nonempty := by
      refine ⟨integralBottomRow 1,?_⟩
      change C≤C ∧ integralBottomRow 1∈Set.range integralBottomRow
      exact ⟨le_rfl,1,rfl⟩
    obtain ⟨v,hv,hmin⟩ := Set.exists_min_image S (integralRowEnergy g) hS hSne
    obtain ⟨N,hN⟩ := hv.2
    refine ⟨N,fun M => ?_⟩
    have hNM : integralRowEnergy g (integralBottomRow N)≤ integralRowEnergy g (integralBottomRow M) := by
      rw [hN]
      by_cases hM : integralRowEnergy g (integralBottomRow M)≤C
      · exact hmin _ ⟨hM,⟨M,rfl⟩⟩
      · exact hv.1.trans (le_of_not_ge hM)
    rw [integral_height_action_matrix,integral_height_action_matrix]
    exact inv_anti₀ (integralRowEnergy_bottom_pos g N) hNM

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O


lemma integralTranslation_action (n : O) (z : ℂ) (v : ℝ) (hv : 0<v) :
    integralComplexMatrix (integralTranslation n) • upperPoint z v hv=
      upperPoint (z+eisEmbedding n) v hv := by
  change (QuotientGroup.mk (integralComplexMatrix (integralTranslation n)*upperSection z v hv) : HyperbolicSpace)=
    QuotientGroup.mk (upperSection (z+eisEmbedding n) v hv)
  apply congrArg (fun g : SL(2,ℂ) => (QuotientGroup.mk g : HyperbolicSpace))
  apply Subtype.ext
  change (integralComplexMatrix (integralTranslation n) : Matrix (Fin 2) (Fin 2) ℂ) *
    (upperSection z v hv : Matrix (Fin 2) (Fin 2) ℂ) =
    (upperSection (z + eisEmbedding n) v hv : Matrix (Fin 2) (Fin 2) ℂ)
  simp only [integralComplexMatrix, Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [integralTranslation,RingHom.mapMatrix_apply,Matrix.map_apply,upperSection,Matrix.mul_apply,
      Fin.sum_univ_two,div_eq_mul_inv] ; ring

lemma integralInversion_height (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHeight (integralComplexMatrix integralInversion • upperPoint z v hv)=
      v/(‖z‖^2+v^2) := by
  have h10 : integralComplexMatrix integralInversion 1 0 = 1 := by
    change eisEmbedding 1 = 1
    exact map_one eisEmbedding
  have h11 : integralComplexMatrix integralInversion 1 1 = 0 := by
    change eisEmbedding 0 = 0
    exact map_zero eisEmbedding
  rw [hyperbolicHeight_action_upperPoint, h10, h11]
  simp

theorem bianchi_ford_cover (w : HyperbolicSpace) :
    ∃M : SL(2,O), ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
      integralComplexMatrix M • w=upperPoint z v hv ∧
      Complex.normSq z≤1/3 ∧ 1≤Complex.normSq z+v^2 ∧
      ∀R : SL(2,O),hyperbolicHeight (integralComplexMatrix R • upperPoint z v hv)≤v := by
  obtain ⟨N,hN⟩ := exists_maximal_integral_height w
  obtain ⟨z,v,hv,hpoint⟩ := upperPoint_surjective (integralComplexMatrix N • w)
  obtain ⟨n,hn⟩ := exists_eisenstein_distance_sq_le_third z
  let M : SL(2,O) := integralTranslation (-n)*N
  let z' := z-eisEmbedding n
  have hMw : integralComplexMatrix M • w=upperPoint z' v hv := by
    dsimp [M]
    rw [map_mul,mul_smul,← hpoint,integralTranslation_action,map_neg]
    rfl
  have hNv : hyperbolicHeight (integralComplexMatrix N • w)=v := by
    rw [← hpoint,hyperbolicHeight_upperPoint]
  have hmax (R : SL(2,O)) :
      hyperbolicHeight (integralComplexMatrix R • upperPoint z' v hv)≤v := by
    have h := hN (R*M)
    rwa [map_mul,mul_smul,hMw,hNv] at h
  have hinv := hmax integralInversion
  rw [integralInversion_height] at hinv
  have hden : 0<‖z'‖^2+v^2 := by positivity
  have hunit : 1≤‖z'‖^2+v^2 := by
    have hm := (div_le_iff₀ hden).mp hinv
    by_contra hh
    have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge hh) hv
    linarith
  refine ⟨M,z',v,hv,hMw,hn,?_,hmax⟩
  simpa only [Complex.normSq_eq_norm_sq] using hunit

theorem bianchi_reduction_height_floor (w : HyperbolicSpace) :
    ∃M : SL(2,O), ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
      integralComplexMatrix M • w=upperPoint z v hv ∧
      Complex.normSq z≤1/3 ∧ Real.sqrt (2/3)≤v := by
  obtain ⟨M,z,v,hv,hMw,hz,hunit,hmax⟩ := bianchi_ford_cover w
  refine ⟨M,z,v,hv,hMw,hz,?_⟩
  apply (Real.sqrt_le_iff).mpr
  exact ⟨hv.le,by linarith⟩


end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O


theorem finiteIndex_ford_cover (H : Subgroup (SL(2,O))) [H.FiniteIndex] :
    ∃S : Finset (SL(2,O)), ∀w : HyperbolicSpace,
      ∃h : H, ∃r∈S, ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
        integralComplexMatrix (h:SL(2,O)) • w=
          integralComplexMatrix r⁻¹ • upperPoint z v hv ∧
        Complex.normSq z≤1/3 ∧ Real.sqrt (2/3)≤v := by
  obtain ⟨S,hS⟩ := finite_right_representatives H
  refine ⟨S,fun w => ?_⟩
  obtain ⟨M,z,v,hv,hMw,hz,hfloor⟩ := bianchi_reduction_height_floor w
  obtain ⟨r,hr,hh⟩ := hS M
  refine ⟨⟨r⁻¹*M,hh⟩,r,hr,z,v,hv,?_,hz,hfloor⟩
  change integralComplexMatrix (r⁻¹*M) • w=_
  rw [map_mul,mul_smul,hMw]

theorem levelThree_ford_cover :
    ∃S : Finset (SL(2,O)), ∀w : HyperbolicSpace,
      ∃h : levelThree, ∃r∈S, ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
        complexMatrix h • w=integralComplexMatrix r⁻¹ • upperPoint z v hv ∧
        Complex.normSq z≤1/3 ∧ Real.sqrt (2/3)≤v := by
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  exact finiteIndex_ford_cover levelThree

theorem globalKubotaKernel_ford_cover :
    ∃S : Finset (SL(2,O)), ∀w : HyperbolicSpace,
      ∃h : globalKubotaKernel, ∃r∈S, ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
        integralComplexMatrix (h:SL(2,O)) • w=integralComplexMatrix r⁻¹ • upperPoint z v hv ∧
        Complex.normSq z≤1/3 ∧ Real.sqrt (2/3)≤v := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact finiteIndex_ford_cover globalKubotaKernel

end CubicEisenstein

end

end OAI

end



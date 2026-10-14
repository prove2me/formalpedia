-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0129_parallel1
-- name    : PNT_ZeroFree_433_0129_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:39:31.333035+00:00
-- url     : https://prove2.me/theorems/8c6da5d0-344f-4823-bc7b-04d80d8b5892
-- title:
--   Zero-free region foundations: QuadraticSieve.PoissonComparison [0129_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.PoissonComparison
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonComparison.lean#L77-L469

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0060
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0082
import Definitions.Def_PNT_ZeroFree_433_0103
import Definitions.Def_PNT_ZeroFree_433_0127_parallel1
import Definitions.Def_PNT_ZeroFree_433_0168_parallel1
import Definitions.Def_PNT_ZeroFree_433_0195_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonComparison.lean
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

namespace CanonicalQuadraticSieve

section

theorem hasSieveExponent_one_of_approximation
    (happrox : ∀ η : ℝ, 0<η → ∃ α : ℝ, α≤1+η ∧ HasSieveExponent α) :
    HasSieveExponent 1 := by
  intro ε hε
  have he : 0<ε/2 := by positivity
  obtain ⟨α,hα,h⟩ := happrox (ε/2) he
  obtain ⟨C,hC,hbound⟩ := h (ε/2) he
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  have hM0 : 0≤M := by linarith
  have hN0 : 0<N := by linarith
  have hMN : 1≤M*N := by nlinarith
  have hNmn : N≤M*N := by nlinarith
  have hQ : 1≤(M*N)^(ε/2) := Real.one_le_rpow hMN he.le
  have hnα : N^α ≤ (M*N)^(ε/2)*N := by
    calc
      _ ≤ N^(1+ε/2) := Real.rpow_le_rpow_of_exponent_le hN hα
      _ = N*N^(ε/2) := by rw [Real.rpow_add hN0,Real.rpow_one]
      _ ≤ N*(M*N)^(ε/2) := by gcongr
      _ = _ := mul_comm _ _
  have hsum : M+N^α ≤ (M*N)^(ε/2)*(M+N) := by
    nlinarith [mul_le_mul_of_nonneg_right hQ hM0]
  calc
    _ ≤ C*(M*N)^(ε/2)*(M+N^α) := hbound M N hM hN
    _ ≤ C*(M*N)^(ε/2)*((M*N)^(ε/2)*(M+N)) := by gcongr
    _ = C*(M*N)^ε*(M+N^(1:ℝ)) := by
      rw [Real.rpow_one]
      have hp : (M*N)^(ε/2)*(M*N)^(ε/2) = (M*N)^ε := by
        rw [← Real.rpow_add (by positivity : 0<M*N)]
        congr 1
        ring
      calc
        _ = C*((M*N)^(ε/2)*(M*N)^(ε/2))*(M+N) := by ring
        _ = _ := by rw [hp]

def bootstrapExponent (n : ℕ) : ℝ := 1+1/((n:ℝ)+1)

theorem bootstrapExponent_gt_one (n : ℕ) : 1<bootstrapExponent n := by
  unfold bootstrapExponent
  have h : (0:ℝ)<1/((n:ℝ)+1) := by positivity
  linarith

theorem bootstrapExponent_le_two (n : ℕ) : bootstrapExponent n≤2 := by
  have h : 1/((n:ℝ)+1)≤(1:ℝ) := by
    apply (div_le_one (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold bootstrapExponent
  linarith

theorem bootstrapExponent_step (n : ℕ) :
    bootstrapExponent (n+1) = 2-1/bootstrapExponent n := by
  unfold bootstrapExponent
  push_cast
  field_simp
  ring

theorem hasSieveExponent_one_of_improvement
    (himprove : ∀ α : ℝ, 1<α → α≤2 → HasSieveExponent α → HasSieveExponent (2-1/α)) :
    HasSieveExponent 1 := by
  have hn : ∀ n : ℕ, HasSieveExponent (bootstrapExponent n) := by
    intro n
    induction n with
    | zero => norm_num [bootstrapExponent]; exact hasSieveExponent_two
    | succ n ih =>
      rw [bootstrapExponent_step]
      exact himprove _ (bootstrapExponent_gt_one n) (bootstrapExponent_le_two n) ih
  apply hasSieveExponent_one_of_approximation
  intro η hη
  obtain ⟨n,hnη⟩ := exists_nat_one_div_lt hη
  refine ⟨bootstrapExponent n,?_,hn n⟩
  unfold bootstrapExponent
  linarith

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

def divisorTwist {n : Type} (cols : n → Ideal O) (a : n → ℂ) (q : Ideal O) : n → ℂ :=
  fun j => a j*quadraticRow (cols j) (idealGenerator q)


lemma finite_centering_identity {ι : Type*} (S : Finset ι) (w R D : ι → ℂ) (c h : ℂ) :
    (∑ q∈S, w q*(c*R q-h*D q)) = c*(∑ q∈S,w q*R q)-h*(∑ q∈S,w q*D q) := by
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring


open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator

theorem divisorTwist_norm_le {n : Type} (cols : n → Ideal O) (a : n → ℂ)
    (q : Ideal O) (j : n) : ‖divisorTwist cols a q j‖≤‖a j‖ := by
  rw [divisorTwist,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)


end

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator


end
section

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
open DivisorBlockCauchy

theorem gcdRaySupport_energy_eq {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    (∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) =
      ∑j, if D∣cols j ∧ columnRay (cols j)=c then ‖a j‖^2 else 0 := by
  classical
  rw [Finset.sum_coe_sort (gcdRaySupport cols a D c) (fun j => ‖a j‖^2)]
  simp only [gcdRaySupport,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hz : a j=0
  · simp only [hz,norm_zero,ne_eq,not_true_eq_false,and_false,ite_self,zero_pow (by decide : 2≠0)]
  · simp only [hz,ne_eq,not_false_eq_true,and_true]

theorem gcdRaySupport_energy_ray_sum {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (D : Ideal O) :
    (∑c : EisensteinEPrimaryPhase.Coord, ∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) =
      ∑j, ‖if D∣cols j then a j else 0‖^2 := by
  classical
  simp_rw [gcdRaySupport_energy_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hd : D∣cols j
  · simp only [hd,true_and,ite_true]
    rw [Finset.sum_eq_single (columnRay (cols j))]
    · simp only [ite_true]
    · intro c hc hne
      exact if_neg (Ne.symm hne)
    · simp
  · simp only [hd,false_and,ite_false,Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0)]

theorem gcdRaySupport_energy_divisor_sum {n : Type} [Fintype n]
    (ε : ℝ) (hε : 0<ε) (S : Finset (Ideal O)) (cols : n → Ideal O)
    (hcols : ∀j, cols j≠0) (a : n → ℂ) (X : ℝ)
    (hX : ∀j, a j≠0 → (Ideal.absNorm (cols j):ℝ)≤X) :
    (∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S,
      ∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) ≤
      (divisorConstant ε hε*X^ε)*∑j, ‖a j‖^2 := by
  classical
  rw [Finset.sum_comm]
  simp_rw [gcdRaySupport_energy_ray_sum]
  apply (divisor_mask_energy S cols hcols a).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hz : a j=0
  · simp only [hz,norm_zero,zero_pow (by decide : 2≠0),mul_zero,le_refl]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply ((IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2 (cols j) (hcols j)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hX j hz) hε.le) (divisorConstant_pos ε hε).le

theorem gcdRaySupport_weighted_sum_bound {n : Type} [Fintype n]
    (ε : ℝ) (hε : 0<ε) (S : Finset (Ideal O)) (cols : n → Ideal O)
    (hcols : ∀j, cols j≠0) (a : n → ℂ) (X C : ℝ) (hC : 0≤C)
    (hX : ∀j, a j≠0 → (Ideal.absNorm (cols j):ℝ)≤X)
    (F : Ideal O → EisensteinEPrimaryPhase.Coord → ℝ)
    (hF : ∀D∈S, ∀c, F D c≤C*∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) :
    (∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S, F D c) ≤
      C*(divisorConstant ε hε*X^ε)*∑j, ‖a j‖^2 := by
  calc
    _ ≤ ∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S,
        C*∑j : gcdRaySupport cols a D c, ‖a j.val‖^2 :=
      Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun D hD => hF D hD c))
    _ = C*(∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S,
        ∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) := by simp only [Finset.mul_sum]
    _ ≤ C*((divisorConstant ε hε*X^ε)*∑j, ‖a j‖^2) :=
      mul_le_mul_of_nonneg_left (gcdRaySupport_energy_divisor_sum ε hε S cols hcols a X hX) hC
    _ = _ := by ring

end

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy

theorem divisorEnergyFactor_diagonal {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0<ε) (N : ℝ) (a : n → ℂ) :
    divisorEnergyFactor ε hε N a a =
      (256*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2)*∑j, ‖a j‖^2 := by
  unfold divisorEnergyFactor
  have hs : 0≤∑j, ‖a j‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [mul_assoc _ (Real.sqrt _) (Real.sqrt _),Real.mul_self_sqrt hs]


end CanonicalQuadraticSieve


end

end OAI

end



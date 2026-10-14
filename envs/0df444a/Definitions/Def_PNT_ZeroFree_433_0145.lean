-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0145
-- name    : PNT_ZeroFree_433_0145
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:06:40.813263+00:00
-- url     : https://prove2.me/theorems/c87db3f5-3cf8-4a12-a498-72acab64f397
-- title:
--   Zero-free region foundations: QuadraticSieve.UniformTailBounds [0145]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.UniformTailBounds
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/UniformTailBounds.lean#L77-L637

import Definitions.Def_PNT_ZeroFree_433_0144
import Definitions.Def_PNT_ZeroFree_433_0145_parallel1
import Definitions.Def_PNT_ZeroFree_433_0145_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/UniformTailBounds.lean
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
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum

theorem product_quadratic_norm_all :
    ∀ε : ℝ, 0<ε → ∃C : ℝ, 0<C ∧ ∀K U B : ℝ,
      1≤K → 1≤U → 1≤B → ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
      ∀β : Ideal O → Ideal O → ℂ, (∀n∈S,∀b∈T,‖β n b‖≤1) →
      (∑k : idealRange K,‖∑n∈S,∑b∈T,quadraticRow k.val (primaryGenerator (n*b))*β n b‖^2)≤
        C*(K*(U*B))^ε*(K+U*B)*(U*B) := by
  intro ε hε
  have hh : 0<ε/2 := by positivity
  have hq : 0<ε/4 := by positivity
  obtain ⟨C,hC,hbound⟩ := bounded_nonzero_quadratic_norm (ε/2) hh
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/4) hq
  refine ⟨C*D^2,by positivity,?_⟩
  intro K U B hK hU hB S T hS hT β hβ
  let X := U*B
  let P := (S×ˢT).image (fun p => p.1*p.2)
  have hX : 1≤X := by dsimp [X]; nlinarith
  have hX0 : 0<X := by linarith
  have hK0 : 0<K := by linarith
  have hp (I : Ideal O) (hI : I∈P) : I≠0 ∧ (Ideal.absNorm I:ℝ)≤X := by
    obtain ⟨⟨n,b⟩,hnb,rfl⟩ := Finset.mem_image.mp hI
    have hm := Finset.mem_product.mp hnb
    refine ⟨mul_ne_zero (hS n hm.1).1 (hT b hm.2).1,?_⟩
    rw [map_mul,Nat.cast_mul]
    exact mul_le_mul (hS n hm.1).2 (hT b hm.2).2 (Nat.cast_nonneg _) (by linarith)
  have hcoeff (I : Ideal O) (hI : I∈P) : ‖productColumnCoefficient S T β I‖≤D*X^(ε/4) := by
    apply (productColumnCoefficient_norm S T β hβ I (hp I hI).1).trans
    apply (hdiv I (hp I hI).1).trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hp I hI).2 hq.le) hD.le
  have hb := hbound K X (D*X^(ε/4)) hK hX (by positivity) P hp (productColumnCoefficient S T β) hcoeff
  simp_rw [productColumnCoefficient_row_sum]
  apply hb.trans
  have hpow : (K*X)^(ε/2)*(X^(ε/4))^2≤(K*X)^ε := by
    have hXP : X≤K*X := by nlinarith
    calc
      _ ≤ (K*X)^(ε/2)*((K*X)^(ε/4))^2 := by gcongr
      _ = _ := by
        rw [pow_two,←mul_assoc,←Real.rpow_add (by positivity : 0<K*X),←Real.rpow_add (by positivity : 0<K*X)]
        congr 1
        ring
  calc
    _ = (C*D^2)*((K*X)^(ε/2)*(X^(ε/4))^2)*(K+X)*X := by ring
    _ ≤ _ := by change _≤(C*D^2)*(K*X)^ε*(K+X)*X; gcongr

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap


open scoped BigOperators Classical


open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalFirstDiagonalCost (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ))
    (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℝ :=
  ∑ b∈s,‖w b‖*(primeProductNorm p b.firstCommon)⁻¹*
    (|Y b| *‖paperRadialFourier W 0‖*
      ∑ G∈(globalFirstRawPool pool b).powerset,
        ‖secondInputCoefficient p hg Ψ (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
          (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
          (globalFirstBlockTest p g ell side b) G‖^2)

include hp in
theorem globalFirstDiagonalCost_nonneg (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ))
    (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    0≤globalFirstDiagonalCost p hg pool s w Ψ m g W ell side Y := by
  unfold globalFirstDiagonalCost
  apply Finset.sum_nonneg
  intro b hb
  have hn := (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon).le
  positivity

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstBlockTest_mode_norm (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool)
    (t : ℝ) (b : GlobalFirstData ι) (G : Finset ι) :
    ‖globalFirstBlockTest p (firstCoreModeProfile g V side t) ell side b G‖ =
      ‖globalFirstBlockTest p (firstCoreBaseProfile g V side) ell side b G‖ := by
  simp only [globalFirstBlockTest,normalizedColumn,norm_div,firstCoreModeProfile,
    JointLogSeparation.frequencyTwist_norm]

include hp in

theorem globalFirstSourceZero_bound
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ,ℂ)) (K ell B F M H : ℝ) (side : Bool) (t : ℝ) :
    ‖globalFirstSourceZero p hg pool s w (globalFirstConcreteCutoff p K ell B F M H side)
      Ψ m (firstCoreModeProfile g V side t) W ell side (globalFirstPooledRow p K ell B F side)‖ ≤
    globalFirstDiagonalCost p hg pool s w Ψ m (firstCoreBaseProfile g V side) W ell side
      (globalFirstPooledRow p K ell B F side) := by
  unfold globalFirstSourceZero globalFirstDiagonalCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  rw [norm_mul,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp _).le]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _)
    (inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp _).le))
  have hh := truncatedSecondZero_norm_le p hg hinj (globalFirstRawPool pool b) Ψ
    (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
    (globalFirstBlockTest p (firstCoreModeProfile g V side t) ell side b)
    W (globalFirstPooledRow p K ell B F side b) (globalFirstConcreteCutoff p K ell B F M H side b)
    (fun G hG E hE => firstCoreSecondCutoff_zero _ _ _ _ _ _ _ _)
  apply hh.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro G hG
  simp only [secondInputCoefficient,norm_mul,globalFirstBlockTest_mode_norm]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalFirstTailCost (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (K ell B F M H : ℝ) (N : ℕ) (side : Bool) : ℝ :=
  ∑ b∈s,
    let lengthScale := 1+globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon*Real.exp M
    let Y := globalFirstPooledRow p K ell B F side b
    ‖w b‖*(primeProductNorm p b.firstCommon)⁻¹*lengthScale^4*Y*(1+lengthScale^3/Y)^2/(1+H)^N

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstTailCost_nonneg (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (K ell B F M H : ℝ) (N : ℕ) (side : Bool)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hH : 0≤H) :
    0≤globalFirstTailCost p s w K ell B F M H N side := by
  unfold globalFirstTailCost
  apply Finset.sum_nonneg
  intro b hb
  dsimp only
  have hn := (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon).le
  have hY : 0<globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB hF _
  positivity
end

theorem globalFirstSourceTail_bound (N : ℕ) (g V W : 𝓢(ℝ,ℂ)) (side : Bool) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
      (Ψ : O →* ℂ) (m : O) (K ell B F M H t : ℝ),
      (∀ a,‖Ψ a‖≤1) → 0<K → 0<ell → 0<B → 0<F → 0≤H → (∀ u,g u≠0 → |u|≤M) →
      ‖globalFirstSourceTail p hp hg hinj pool s w (globalFirstConcreteCutoff p K ell B F M H side)
        Ψ m (firstCoreModeProfile g V side t) W ell side (globalFirstPooledRow p K ell B F side)‖ ≤
      C*globalFirstTailCost p s w K ell B F M H N side := by
  obtain ⟨C,hC,hbound⟩ := full_uniform_firstCoreSecondCutoff_tail_fixed_source N g V W side
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc pool s w Ψ m K ell B F M H t hΨ hK hell hB hF hH hgM
  unfold globalFirstSourceTail globalFirstTailCost
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  dsimp only
  rw [norm_mul,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp _).le]
  have hX : 0<globalFirstBlockColumnScale p ell side b :=
    div_pos hell (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))
  have hY : 0<globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB hF _
  have hh := hbound p hp hg hinj hc (pool\(b.cube.support∪b.common)) b.firstCommon Ψ
    (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
    t (globalFirstBlockColumnScale p ell side b) (globalFirstPooledRow p K ell B F side b) M H
    hΨ hX hY hH hgM
  have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg (norm_nonneg (w b))
    (inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon).le))
  apply hh'.trans_eq
  ring

end SecondPassArithmetic

end

end OAI

end



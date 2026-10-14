-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0144
-- name    : PNT_ZeroFree_433_0144
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:05:07.887204+00:00
-- url     : https://prove2.me/theorems/80964847-0fc1-4e37-a088-f29465471196
-- title:
--   Zero-free region foundations: QuadraticSieve.ProductColumns [0144]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.ProductColumns
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/ProductColumns.lean#L77-L710

import Definitions.Def_PNT_ZeroFree_433_0143
import Definitions.Def_PNT_ZeroFree_433_0144_parallel1
import Definitions.Def_PNT_ZeroFree_433_0144_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/ProductColumns.lean
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


theorem product_quadratic_norm :
    ∀ε : ℝ, 0<ε → ∃C : ℝ, 0<C ∧ ∀K U B : ℝ,
      1≤K → 1≤U → 1≤B → ∀S T : Finset (Ideal O),
      (∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,Supported I ∧ (Ideal.absNorm I:ℝ)≤B) →
      ∀β : Ideal O → Ideal O → ℂ, (∀n∈S,∀b∈T,‖β n b‖≤1) →
      (∑k : idealRange K,‖∑n∈S,∑b∈T,quadraticRow k.val (primaryGenerator (n*b))*β n b‖^2)≤
        C*(K*(U*B))^ε*(K+U*B)*(U*B) := by
  intro ε hε
  have hh : 0<ε/2 := by positivity
  have hq : 0<ε/4 := by positivity
  obtain ⟨C,hC,hbound⟩ := bounded_supported_quadratic_norm (ε/2) hh
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/4) hq
  refine ⟨C*D^2,by positivity,?_⟩
  intro K U B hK hU hB S T hS hT β hβ
  let X := U*B
  let P := (S×ˢT).image (fun p => p.1*p.2)
  have hX : 1≤X := by dsimp [X]; nlinarith
  have hX0 : 0<X := by linarith
  have hK0 : 0<K := by linarith
  have hp (I : Ideal O) (hI : I∈P) : Supported I ∧ (Ideal.absNorm I:ℝ)≤X := by
    obtain ⟨⟨n,b⟩,hnb,rfl⟩ := Finset.mem_image.mp hI
    have hm := Finset.mem_product.mp hnb
    refine ⟨(supported_mul_iff n b).mpr ⟨(hS n hm.1).1,(hT b hm.2).1⟩,?_⟩
    rw [map_mul,Nat.cast_mul]
    exact mul_le_mul (hS n hm.1).2 (hT b hm.2).2 (Nat.cast_nonneg _) (by linarith)
  have hcoeff (I : Ideal O) (hI : I∈P) : ‖productColumnCoefficient S T β I‖≤D*X^(ε/4) := by
    apply (productColumnCoefficient_norm S T β hβ I (hp I hI).1.1).trans
    apply (hdiv I (hp I hI).1.1).trans
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

namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge


theorem short_completed_energy {κ : Type*} [Fintype κ]
    (Ψ : κ → O →* ℂ) (hΨ : ∀k z,‖Ψ k z‖≤1)
    (W : ℝ → ℂ) (X H₀ A : ℝ) (hA : 0≤A)
    (hcompleted : ∀H∈shortCubeRange H₀,
      (∑k,‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤A) :
    (∑k,‖shortCompletedSum (Ψ k) W X H₀‖^2)≤
      A*(256*(columnDyadicLength H₀+1:ℝ))^2 := by
  let S := shortCubeRange H₀
  let lengthScale : ℝ := ∑H∈S,1/(Ideal.absNorm H:ℝ)
  have hS (H : Ideal O) (hH : H∈S) : H≠0 := ((mem_shortCubeRange H₀ H).mp hH).1
  have hn (H : Ideal O) (hH : H∈S) : 0<(Ideal.absNorm H:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hS H hH (Ideal.absNorm_eq_zero_iff.mp hz))
  have hL : 0≤lengthScale := Finset.sum_nonneg (fun H hH => by positivity)
  have hb (k : κ) : ‖shortCompletedSum (Ψ k) W X H₀‖^2≤
      lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2 := by
    rw [shortCompletedSum_eq]
    apply (ideal_reciprocal_cauchy S hS _).trans
    apply mul_le_mul_of_nonneg_left _ hL
    apply Finset.sum_le_sum
    intro H hH
    rw [norm_mul]
    calc
      _ ≤ (Ideal.absNorm H:ℝ)*((1/(Ideal.absNorm H:ℝ))*‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖)^2 := by
        gcongr
        exact cube_inverse_weight_norm (Ψ k) (hΨ k) H
      _ = _ := by field_simp [(hn H hH).ne']
  have hsum : (∑k,‖shortCompletedSum (Ψ k) W X H₀‖^2)≤A*lengthScale^2 := by
    calc
      _ ≤ ∑k,lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2 :=
        Finset.sum_le_sum (fun k _ => hb k)
      _ = lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*∑k,‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro H hH
        rw [←Finset.mul_sum]
      _ ≤ lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*A := by
        gcongr with H hH
        exact hcompleted H hH
      _ = A*lengthScale^2 := by rw [←Finset.sum_mul]; change lengthScale*(lengthScale*A)=A*lengthScale^2; ring
  have hbound : lengthScale≤256*(columnDyadicLength H₀+1:ℝ) :=
    finite_inverse_norm_sum S H₀ hS (fun H hH => ((mem_shortCubeRange H₀ H).mp hH).2.le)
  exact hsum.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hbound 2) hA)

end

open ActualEisensteinCubic CanonicalQuadraticSieve


theorem short_completed_branch {κ : Type*} [Fintype κ]
    (Ψ : κ → O →* ℂ) (hΨ : ∀k z,‖Ψ k z‖≤1)
    (W : ℝ → ℂ) (Z K R X F A : ℝ)
    (hZ : 1≤Z) (hK : 1≤K) (hR : 1≤R) (hF : 1≤F)
    (hFZ : F≤Z^(1/1000:ℝ)) (hA : 0≤A)
    (hmargin : K*R≤X*F*Z^(-(1/40:ℝ)))
    (hcompleted : ∀H∈shortCubeRange (Z^(1/1000:ℝ)),
      (∑k,‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤
        A*(K+K^2*R*F*(Ideal.absNorm H:ℝ)^3/X)) :
    (∑k,‖shortCompletedSum (Ψ k) W X (Z^(1/1000:ℝ))‖^2)≤
      (2*A*K)*(256*(columnDyadicLength (Z^(1/1000:ℝ))+1:ℝ))^2 := by
  apply short_completed_energy Ψ hΨ W X _ (2*A*K) (by positivity)
  intro H hH
  have hs := (mem_shortCubeRange _ H).mp hH
  have hn : 1≤(Ideal.absNorm H:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hs.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hsc := short_cube_scales Z K R X F (Ideal.absNorm H:ℝ)
    hZ hK hR hF hFZ hn hs.2.le hmargin
  apply (hcompleted H hH).trans
  nlinarith

theorem short_completed_average {κ : Type*} [Fintype κ]
    (Z K R X F A : ℝ) (hZ : 1≤Z) (hK : 1≤K) (hR : 1≤R) (hF : 1≤F)
    (hFZ : F≤Z^(1/1000:ℝ)) (hA : 0≤A)
    (hmargin : K*R≤X*F*Z^(-(1/40:ℝ)))
    (Ψ : idealRange F → κ → O →* ℂ) (hΨ : ∀f k z,‖Ψ f k z‖≤1) (W : ℝ → ℂ)
    (hcompleted : ∀f : idealRange F, ∀H∈shortCubeRange (Z^(1/1000:ℝ)),
      (∑k,‖completedT (Ψ f k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤
        A*(K+K^2*R*(Ideal.absNorm f.val:ℝ)*(Ideal.absNorm H:ℝ)^3/X)) :
    (∑f : idealRange F,∑k,‖shortCompletedSum (Ψ f k) W X (Z^(1/1000:ℝ))‖^2)/F≤
      256*A*K*(256*(columnDyadicLength (Z^(1/1000:ℝ))+1:ℝ))^2 := by
  have hZ0 : 0<Z := by linarith
  have hh : 1≤Z^(1/1000:ℝ) := Real.one_le_rpow hZ (by norm_num)
  have hx := (short_cube_scales Z K R X F 1 hZ hK hR hF hFZ le_rfl hh hmargin).1
  norm_num at hx
  have hX : 0<X := by linarith
  let B := (256*(columnDyadicLength (Z^(1/1000:ℝ))+1:ℝ))^2
  have hb (f : idealRange F) :
      (∑k,‖shortCompletedSum (Ψ f k) W X (Z^(1/1000:ℝ))‖^2)≤2*A*K*B := by
    apply short_completed_branch (Ψ f) (hΨ f) W Z K R X F A hZ hK hR hF hFZ hA hmargin
    intro H hH
    apply (hcompleted f H hH).trans
    gcongr
    exact (mem_idealRange.mp f.property).2
  have hc : ((idealRange F).card:ℝ)≤128*F := by
    apply DescentFiberCost.finite_ideal_count_real _ _ hF
    · intro I hI
      exact (mem_idealRange.mp hI).1.1
    · intro I hI
      exact (mem_idealRange.mp hI).2
  have hsum : (∑f : idealRange F,∑k,‖shortCompletedSum (Ψ f k) W X (Z^(1/1000:ℝ))‖^2)≤
      (128*F)*(2*A*K*B) := by
    calc
      _ ≤ ∑_f : idealRange F,2*A*K*B := Finset.sum_le_sum (fun f _ => hb f)
      _ = ((idealRange F).card:ℝ)*(2*A*K*B) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by dsimp [B]; positivity)
  change _≤256*A*K*B
  calc
    _ ≤ ((128*F)*(2*A*K*B))/F := div_le_div_of_nonneg_right hsum (by linarith)
    _ = _ := by field_simp; ring

theorem short_completed_normalized_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (Z K R X F A : ℝ),
      1≤Z → 1≤K → 1≤R → 1≤F → F≤Z^(1/1000:ℝ) → 0≤A →
      K*R≤X*F*Z^(-(1/40:ℝ)) →
      ∀ {κ : Type*} [Fintype κ],
      ∀ (Ψ : idealRange F → κ → O →* ℂ), (∀f k z,‖Ψ f k z‖≤1) →
      ∀W : ℝ → ℂ,
      (∀f : idealRange F, ∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        (∑k,‖completedT (Ψ f k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤
          A*(K+K^2*R*(Ideal.absNorm f.val:ℝ)*(Ideal.absNorm H:ℝ)^3/X)) →
      (∑f : idealRange F,∑k,‖shortCompletedSum (Ψ f k) W X (Z^(1/1000:ℝ))‖^2)/F≤
        C*A*K*Z^ε := by
  let D := 256*(2+1/((ε/2)*Real.log 2))
  have hD : 0<D := by have hlog : 0<Real.log 2 := Real.log_pos (by norm_num); dsimp [D]; positivity
  refine ⟨256*D^2,by positivity,?_⟩
  intro Z K R X F A hZ hK hR hF hFZ hA hmargin κ _ Ψ hΨ W hcompleted
  have hz : 1≤Z^(1/1000:ℝ) := Real.one_le_rpow hZ (by norm_num)
  have hZ0 : 0<Z := by linarith
  have hzZ : Z^(1/1000:ℝ)≤Z := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ (show (1/1000:ℝ)≤1 by norm_num)
  have hl : 256*(columnDyadicLength (Z^(1/1000:ℝ))+1:ℝ)≤D*Z^(ε/2) := by
    apply (mul_le_mul_of_nonneg_left (columnDyadicLength_small_power (ε/2) (by positivity) _ hz) (by norm_num : (0:ℝ)≤256)).trans
    have hp := Real.rpow_le_rpow (by positivity : 0≤Z^(1/1000:ℝ)) hzZ (show 0≤ε/2 by positivity)
    calc
      _ = D*(Z^(1/1000:ℝ))^(ε/2) := by dsimp [D]; ring
      _ ≤ D*Z^(ε/2) := mul_le_mul_of_nonneg_left hp hD.le
  have hb := short_completed_average Z K R X F A hZ hK hR hF hFZ hA hmargin Ψ hΨ W hcompleted
  apply hb.trans
  calc
    _ ≤ 256*A*K*(D*Z^(ε/2))^2 := by gcongr
    _ = _ := by
      have hp : (Z^(ε/2))^2=Z^ε := by
        rw [pow_two,←Real.rpow_add hZ0]
        congr 1
        ring
      rw [mul_pow,hp]
      ring

end CompletedGauss

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel


theorem bounded_nonzero_quadratic_norm :
    ∀ε : ℝ, 0<ε → ∃C : ℝ, 0<C ∧ ∀K X lengthScale : ℝ,
      1≤K → 1≤X → 0≤lengthScale → ∀S : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤X) →
      ∀a : Ideal O → ℂ, (∀I∈S,‖a I‖≤lengthScale) →
      (∑k : idealRange K,‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2)≤
        C*(K*X)^ε*(K+X)*X*lengthScale^2 := by
  intro ε hε
  let deltaLoss := ε/3
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  obtain ⟨C,hC,hsharp⟩ := sieveNorm_sharp deltaLoss hδ
  let D : ℝ := 256*(2+1/(deltaLoss*Real.log 2))
  have hD : 0<D := by have hlog : 0<Real.log 2 := Real.log_pos (by norm_num); dsimp [D]; positivity
  refine ⟨512*C*D^2,by positivity,?_⟩
  intro K X lengthScale hK hX hL S hS a ha
  let T := S.image squarePart
  let R : ℝ := ∑A∈T,1/(Ideal.absNorm A:ℝ)
  have hK0 : 0<K := by linarith
  have hX0 : 0<X := by linarith
  have hP0 : 0<K*X := by positivity
  have hprop (A : Ideal O) (hA : A∈T) := columnSquareParts_nonzero_bounds S X hS A hA
  have hT0 : ∀A∈T,A≠0 := fun A hA => (hprop A hA).1
  have hR : 0≤R := by dsimp [R]; positivity
  have hRL : R≤D*X^deltaLoss := by
    apply (finite_inverse_norm_sum T X hT0 (fun A hA => (hprop A hA).2.2.1)).trans
    have hh := columnDyadicLength_small_power deltaLoss hδ X hX
    dsimp [D]
    nlinarith
  let F : ℝ := 512*C*(K*X)^deltaLoss*(K+X)*X*lengthScale^2
  have hF : 0≤F := by dsimp [F]; positivity
  have hf (A : Ideal O) (hA : A∈T) :
      (Ideal.absNorm A:ℝ)*(∑k : idealRange K,‖∑I∈columnSquareFiber S A,
        quadraticRow k.val (primaryGenerator I)*a I‖^2)≤F/(Ideal.absNorm A:ℝ) := by
    have hp := hprop A hA
    have hn : 0<(Ideal.absNorm A:ℝ) := by linarith [hp.2.1]
    let Y := X/(Ideal.absNorm A:ℝ)^2
    have hY : 1≤Y := hp.2.2.2
    have hYX : Y≤X := div_le_self hX0.le (one_le_pow₀ hp.2.1)
    have hb : sieveNorm Y K≤C*(K*X)^deltaLoss*(K+X) := by
      apply (hsharp Y K hY hK).trans
      have hprod : Y*K≤K*X := by nlinarith
      have hpw := Real.rpow_le_rpow (by positivity : 0≤Y*K) hprod hδ.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpw hC.le) (by linarith)
        (by positivity) (by positivity)
    have hea : (∑I∈columnSquareFiber S A,‖a I‖^2)≤128*Y*lengthScale^2 := by
      calc
        _ ≤ ∑_I∈columnSquareFiber S A,lengthScale^2 := by
          apply Finset.sum_le_sum
          intro I hI
          exact pow_le_pow_left₀ (norm_nonneg _) (ha I (Finset.mem_filter.mp hI).1) 2
        _ = ((columnSquareFiber S A).card:ℝ)*lengthScale^2 := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (columnSquareFiber_nonzero_card S X hS A hY) (sq_nonneg _)
    have he := columnSquareFiber_all_energy S X K hS A a
    calc
      _ ≤ (Ideal.absNorm A:ℝ)*(4*sieveNorm Y K*(∑I∈columnSquareFiber S A,‖a I‖^2)) :=
        mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
      _ ≤ (Ideal.absNorm A:ℝ)*((4*C*(K*X)^deltaLoss*(K+X))*(128*Y*lengthScale^2)) := by
        have h4 := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤4)
        have hh := mul_le_mul h4 hea (by positivity) (by positivity)
        have hw := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α:=ℝ) (Ideal.absNorm A))
        convert! hw using 1 ; ring
      _ = F/(Ideal.absNorm A:ℝ) := by dsimp [F,Y]; field_simp [hn.ne'] ; ring
  have hsplit (k : idealRange K) :
      (∑I∈S,quadraticRow k.val (primaryGenerator I)*a I)=
      ∑A∈T,∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I := by
    exact (Finset.sum_fiberwise_of_maps_to (fun I hI => Finset.mem_image_of_mem squarePart hI) _).symm
  have hcauchy (k : idealRange K) :
      ‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2≤
      R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I‖^2 := by
    rw [hsplit]
    exact ideal_reciprocal_cauchy T hT0 _
  have htotal : (∑k : idealRange K,‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2)≤F*R^2 := by
    calc
      _ ≤ ∑k : idealRange K,R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,
          quadraticRow k.val (primaryGenerator I)*a I‖^2 := Finset.sum_le_sum (fun k _ => hcauchy k)
      _ = R*∑A∈T,(Ideal.absNorm A:ℝ)*∑k : idealRange K,‖∑I∈columnSquareFiber S A,
          quadraticRow k.val (primaryGenerator I)*a I‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro A hA
        rw [←Finset.mul_sum]
      _ ≤ R*∑A∈T,F/(Ideal.absNorm A:ℝ) := by gcongr with A hA; exact hf A hA
      _ = F*R^2 := by
        simp_rw [div_eq_mul_inv]
        rw [←Finset.mul_sum]
        dsimp [R]
        simp only [one_div]
        ring
  have hpower : (K*X)^deltaLoss*(X^deltaLoss)^2≤(K*X)^ε := by
    have hXP : X≤K*X := by nlinarith
    calc
      _ ≤ (K*X)^deltaLoss*((K*X)^deltaLoss)^2 := by gcongr
      _ = (K*X)^ε := by
        rw [pow_two,←mul_assoc,←Real.rpow_add hP0,←Real.rpow_add hP0]
        congr 1
        dsimp [deltaLoss]
        ring
  apply htotal.trans
  calc
    _ ≤ F*(D*X^deltaLoss)^2 := by gcongr
    _ = (512*C*D^2)*((K*X)^deltaLoss*(X^deltaLoss)^2)*(K+X)*X*lengthScale^2 := by dsimp [F]; ring
    _ ≤ _ := by gcongr

end CanonicalQuadraticSieve

end

end OAI

end



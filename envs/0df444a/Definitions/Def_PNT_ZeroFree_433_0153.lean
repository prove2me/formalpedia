-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0153
-- name    : PNT_ZeroFree_433_0153
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:21:41.176647+00:00
-- url     : https://prove2.me/theorems/b43c8d3a-d27c-4f3e-9432-8be75ef0fbb6
-- title:
--   Zero-free region foundations: CubicSieve.NormalizedMass [0153]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.NormalizedMass
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/NormalizedMass.lean#L312-L696

import Definitions.Def_PNT_ZeroFree_433_0153_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/NormalizedMass.lean
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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic


open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

theorem globalFirstDiagonalCost_parent_bound (ε : ℝ) (hε : 0<ε)
    (g W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : ∀t,g t≠0 → |t|≤M) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
      (Ψ : O →* ℂ) (m : O) (Γ K ell B F U : ℝ) (side : Bool),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 1≤U → ell*Real.exp M≤U →
      (∀z,‖Ψ z‖≤1) → (∀b∈s,0≤w b ∧ w b≤Γ) → (∀b∈s,GlobalFirstAdmissible b) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      globalFirstDiagonalCost p hg pool s
        (fun b => ((w b*globalFirstCoefficient p K ell B F side b : ℝ) : ℂ))
        Ψ m g W ell side (globalFirstPooledRow p K ell B F side)≤
          C*Γ*(ell*B^3*F)*(B*U)^ε := by
  obtain ⟨Cg,hCg,hmass⟩ := full_uniform_normalized_second_mass g M hM
  obtain ⟨Cd,hCd,hcount⟩ := globalFirstData_harmonic_sum (ε/3) (by positivity)
  obtain ⟨Cp,hCp,hpowers⟩ := globalDiagonalPowers ε hε
  let P := Cd*Cg*‖paperRadialFourier W 0‖*(Real.exp 1)^3
  have hP : 0≤P := by dsimp [P]; positivity
  refine ⟨P*Cp+1,by positivity,?_⟩
  intro ι _ p hp _ hg hinj pool s w Ψ m Γ K ell B F U side
    hΓ hK hell hB hF hU hellU hΨ hw hs hb1 hb2
  have hB0 : 0<B := by linarith
  let T := s.filter (fun b => primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U)
  let θ := fun b : GlobalFirstData ι =>
    (1/primeProductNorm p b.common)*(1/primeProductNorm p b.firstCommon)*
      (1/‖eisEmbedding (∏i∈cubeActiveSupport b.cube.support
        (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖)
  have ht (b : GlobalFirstData ι) (hb : b∈T) : b∈s := (Finset.mem_filter.mp hb).1
  have hsum := hcount p hp hinj T B U hB hU
    (fun b hb => hs b (ht b hb)) (fun b hb => (Finset.mem_filter.mp hb).2.1)
    (fun b hb => (Finset.mem_filter.mp hb).2.2)
    (fun b hb => hb1 b (ht b hb)) (fun b hb => hb2 b (ht b hb))
  change (∑b∈T,θ b)≤_ at hsum
  rw [globalFirstDiagonalCost_eq_supported p hp hg pool s _ Ψ m g W ell M U hell hM hellU side]
  change globalFirstDiagonalCost p hg pool T _ Ψ m g W ell side _≤_
  have hterm (b : GlobalFirstData ι) (hb : b∈T) :
      ‖((w b*globalFirstCoefficient p K ell B F side b : ℝ) : ℂ)‖*(primeProductNorm p b.firstCommon)⁻¹*
        (|globalFirstPooledRow p K ell B F side b| *‖paperRadialFourier W 0‖*
          globalFirstColumnMass p hg pool b Ψ m g ell side)≤
        (Γ*Cg*‖paperRadialFourier W 0‖*(Real.exp 1)^3*ell*B^2*F)*θ b := by
    have htpos := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon
    have hcpos := FirstPassCubeLabels.primeProductNorm_pos p hp b.common
    have hapos := FirstPassCubeLabels.primeProductNorm_pos p hp (b.cube.sideDivisor side)
    have hX : 0<globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon := by
      unfold globalFirstBlockColumnScale
      positivity
    have hm := hmass p hp hg hinj (globalFirstRawPool pool b) Ψ hΨ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon) hX
    change globalFirstColumnMass p hg pool b Ψ m g ell side≤Cg at hm
    have hm0 : 0≤globalFirstColumnMass p hg pool b Ψ m g ell side :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hc : 0≤globalFirstCoefficient p K ell B F side b :=
      globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB0 hF _
    have hY : 0<globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB0 hF _
    have hwb := hw b (ht b hb)
    have hwΓ := hwb.2
    rw [Complex.norm_real,Real.norm_of_nonneg (mul_nonneg hwb.1 hc),abs_of_pos hY]
    have hsc := globalFirst_diagonal_scalar p hp K ell B F hK hell hB0 hF side b
    have hsc' : globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹≤((Real.exp 1)^3*ell*B^2*F)*θ b := by
      convert! hsc using 1 ; dsimp [θ] ; ring
    calc
      _ = (w b*‖paperRadialFourier W 0‖*globalFirstColumnMass p hg pool b Ψ m g ell side)*
          (globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*(primeProductNorm p b.firstCommon)⁻¹) := by ring
      _ ≤ (Γ*‖paperRadialFourier W 0‖*Cg)*
          (globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*(primeProductNorm p b.firstCommon)⁻¹) := by gcongr
      _ ≤ (Γ*‖paperRadialFourier W 0‖*Cg)*(((Real.exp 1)^3*ell*B^2*F)*θ b) :=
        mul_le_mul_of_nonneg_left hsc' (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (Γ*Cg*‖paperRadialFourier W 0‖*(Real.exp 1)^3*ell*B^2*F)*(∑b∈T,θ b) := by
      unfold globalFirstDiagonalCost
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    _ ≤ (Γ*Cg*‖paperRadialFourier W 0‖*(Real.exp 1)^3*ell*B^2*F)*
        (Cd*B^(1+ε/3)*(U*B^2)^(ε/3)*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = P*Γ*(ell*B^3*F)*
        (B^(ε/3)*(U*B^2)^(ε/3)*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2) := by
      rw [Real.rpow_add hB0,Real.rpow_one]
      dsimp [P]
      ring
    _ ≤ P*Γ*(ell*B^3*F)*(Cp*(B*U)^ε) :=
      mul_le_mul_of_nonneg_left (hpowers B U hB hU) (by positivity)
    _ ≤ (P*Cp+1)*Γ*(ell*B^3*F)*(B*U)^ε := by
      calc
        _ = (P*Cp)*(Γ*(ell*B^3*F)*(B*U)^ε) := by ring
        _ ≤ (P*Cp+1)*(Γ*(ell*B^3*F)*(B*U)^ε) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CompletedGauss


open ActualEisensteinCubic UniqueFactorizationMonoid


theorem nonresidual_prime_square_dvd (I Q P : Ideal O) (hI : I≠0) (hP : Prime P)
    (hd : P∣I) (hr : ¬P∣rowResidualPart I Q) :
    P^2∣rowPowerfulPart I*(rowMaskPart I Q)^2 := by
  have hh : P∣rowPowerfulPart I*rowMaskPart I Q := by
    rw [←row_powerful_mask_residual_product I Q hI] at hd
    exact (hP.dvd_mul.mp hd).resolve_right hr
  rcases hP.dvd_mul.mp hh with ha|ht
  · exact dvd_mul_of_dvd_left (prime_square_dvd_powerful _ _ (rowPowerfulPart_powerful I) hP ha) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ht 2) _


theorem nonresidual_gain_product_dvd {ι : Type*} [Fintype ι]
    (I Q : Ideal O) (hI : I≠0) (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q) :
    (∏i,nonresidualGain I (P i)) ∣ rowPowerfulPart I*(rowMaskPart I Q)^2*Q := by
  apply Fintype.prod_dvd_of_coprime
  · intro i j hij
    change IsCoprime (nonresidualGain I (P i)) (nonresidualGain I (P j))
    unfold nonresidualGain
    by_cases hi : P i∣I
    · rw [if_pos hi]
      by_cases hj : P j∣I
      · rw [if_pos hj]
        exact (hcop hij).pow
      · rw [if_neg hj]
        exact (hcop hij).pow_left
    · rw [if_neg hi]
      by_cases hj : P j∣I
      · rw [if_pos hj]
        exact (hcop hij).pow_right
      · rw [if_neg hj]
        exact hcop hij
  · intro i
    have hp : Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
    by_cases hi : P i∣I
    · rw [nonresidualGain,if_pos hi]
      exact dvd_mul_of_dvd_left (nonresidual_prime_square_dvd I Q (P i) hI hp hi (hres i)) Q
    · rw [nonresidualGain,if_neg hi]
      exact dvd_mul_of_dvd_right ((hp.dvd_mul.mp (hpool i)).resolve_left hi) _

open ActualEisensteinCubic UniqueFactorizationMonoid


theorem reflectionConductorCost_bound {ι : Type*} [Fintype ι]
    (I F Q : Ideal O) (hI : I≠0) (hQ : Q≠0)
    (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q) (e : ι→Fin 3) :
    reflectionConductorCost P (fun i => completedLocalExponent I F (P i)) e≤
      (Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ)^2*(Ideal.absNorm Q:ℝ) := by
  rw [reflectionConductorCost_eq_prod P (fun i => NeZero.ne (P i))]
  have hfirst : (∏i,reflectionLocalCost (Ideal.absNorm (P i):ℝ) (completedLocalExponent I F (P i)) (e i))≤
      (Ideal.absNorm (∏i,nonresidualGain I (P i)):ℝ) := by
    rw [map_prod,Nat.cast_prod]
    exact Finset.prod_le_prod (fun i _ => reflectionLocalCost_nonneg _ (Nat.cast_nonneg _) _ _)
      (fun i _ => reflectionLocalCost_le_gain I F (P i) hI (Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance) (e i))
  apply hfirst.trans
  have hd := nonresidual_gain_product_dvd I Q hI P hcop hpool hres
  have hN : 0<Ideal.absNorm (rowPowerfulPart I*(rowMaskPart I Q)^2*Q) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hne := mul_ne_zero (mul_ne_zero (rowPowerfulPart_ne_zero I)
      (pow_ne_zero 2 (squarefreeMaskPart_ne_zero (rowSimplePart I) Q))) hQ
    exact hne (Ideal.absNorm_eq_zero_iff.mp hz)
  have hb := Nat.le_of_dvd hN (map_dvd Ideal.absNorm hd)
  have hr : (Ideal.absNorm (∏i,nonresidualGain I (P i)):ℝ)≤
      (Ideal.absNorm (rowPowerfulPart I*(rowMaskPart I Q)^2*Q):ℝ) := by exact_mod_cast hb
  simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using hr

end CompletedGauss

end

end OAI

end



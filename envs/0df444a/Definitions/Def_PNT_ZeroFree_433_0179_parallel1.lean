-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0179_parallel1
-- name    : PNT_ZeroFree_433_0179_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:29:29.952985+00:00
-- url     : https://prove2.me/theorems/25c014bc-8dee-4994-b9ab-5fd6cfcd045b
-- title:
--   Zero-free region foundations: MeanSquare.RetainedDensity [0179_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.MeanSquare.RetainedDensity
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/RetainedDensity.lean#L84-L455

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0066
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0130
import Definitions.Def_PNT_ZeroFree_433_0135_parallel1
import Definitions.Def_PNT_ZeroFree_433_0139_parallel1
import Definitions.Def_PNT_ZeroFree_433_0149_parallel2
import Definitions.Def_PNT_ZeroFree_433_0174_parallel1
import Definitions.Def_PNT_ZeroFree_433_0223_parallel1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel2
import Definitions.Def_PNT_ZeroFree_433_0246_parallel1
import Definitions.Def_PNT_ZeroFree_433_0249_parallel1
import Definitions.Def_PNT_ZeroFree_433_0255_parallel1
import Definitions.Def_PNT_ZeroFree_433_0259_parallel1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel2
import Definitions.Def_PNT_ZeroFree_433_0280_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/RetainedDensity.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace InitialMeanSquare

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

section

open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (primeProductNorm)

lemma initialLogLabel_ge_one (j : SecondLogIndex) : 1 ≤ initialLogLabel j :=
  one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (normLogScale_ge_one _))
    (Real.one_le_exp (by norm_num))

lemma initialLogColumn_pos (Z B : ℝ) (j : SecondLogIndex) (hZ : 0 < Z) (hB : 0 < B) :
    0 < initialLogColumn Z B j :=
  div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hB)

lemma initialLogColumn_le (Z B : ℝ) (j : SecondLogIndex) (hZ : 0 ≤ Z) (hB : 1 ≤ B) :
    initialLogColumn Z B j ≤ Z := div_le_self hZ
  (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (normLogScale_ge_one _)) hB)

lemma initialLogLabel_cap (U Kmax : ℝ) (hU : 1 ≤ U) (j : SecondLogIndex)
    (hj : j ∈ secondLogBinBox U Kmax) : initialLogLabel j ≤ U^2*Real.exp 2 := by
  have hj' : j.1 < normLogBin U+1 ∧ j.2.1 < normLogBin U+1 ∧ j.2.2 < normLogBin Kmax+1 := by
    simpa only [secondLogBinBox,Finset.mem_product,Finset.mem_range] using hj
  have he : secondLogE j ≤ U := by
    apply le_trans _ (normLogBin_scale_bounds U hU).1
    unfold secondLogE normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast Nat.le_of_lt_succ hj'.1
  have hv : secondLogV j ≤ U := by
    apply le_trans _ (normLogBin_scale_bounds U hU).1
    unfold secondLogV normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast Nat.le_of_lt_succ hj'.2.1
  unfold initialLogLabel
  simpa only [pow_two] using mul_le_mul_of_nonneg_right
    (mul_le_mul he hv (normLogScale_pos _).le (zero_le_one.trans hU)) (Real.exp_pos 2).le

theorem initial_radial_invariant (Z B c σ θ deltaLoss κ : ℝ) (j : SecondLogIndex)
    (hZ : 1 ≤ Z) (hB : 0 < B) (hc : 0 ≤ c) (hcZ : c ≤ Z^deltaLoss)
    (hmargin : deltaLoss+θ ≤ σ-κ)
    (hrad : initialRadial Z (Z^(1+σ)) B j ≤ Z^θ) :
    (secondLogK j*Real.exp 2)*(c*B) ≤
      initialLogColumn Z B j*initialLogLabel j*Z^(-κ) := by
  have hZ0 := zero_lt_one.trans_le hZ
  have hH : 0 < Z^(1+σ) := Real.rpow_pos_of_pos hZ0 _
  have hm : 0 < initialLogColumn Z B j*initialLogLabel j := by
    rw [initial_log_mass Z B hB.ne' j]
    positivity
  have he : Z/Z^(1+σ)=Z^(-σ) := by
    rw [show -σ=(1 : ℝ)-(1+σ) by ring,Real.rpow_sub hZ0,Real.rpow_one]
  have hid : (secondLogK j*Real.exp 2)*(c*B)/(initialLogColumn Z B j*initialLogLabel j)=
      c*(Z/(Z^(1+σ)))*(Z^(1+σ)*secondLogK j*B^2/Z^2) := by
    rw [initial_log_mass Z B hB.ne' j]
    have hE := (Real.exp_pos (2 : ℝ)).ne'
    have hz := hZ0.ne'
    have hh := hH.ne'
    field_simp

  rw [mul_comm (initialLogColumn Z B j*initialLogLabel j)]
  apply (div_le_iff₀ hm).mp
  rw [hid,he]
  calc
    c*Z^(-σ)*(Z^(1+σ)*secondLogK j*B^2/Z^2) ≤ c*Z^(-σ)*Z^θ :=
      mul_le_mul_of_nonneg_left hrad (mul_nonneg hc (Real.rpow_nonneg hZ0.le _))
    _ ≤ Z^deltaLoss*Z^(-σ)*Z^θ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcZ (Real.rpow_nonneg hZ0.le _)) (Real.rpow_nonneg hZ0.le _)
    _ = Z^(deltaLoss-σ+θ) := by rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]; congr 1
    _ ≤ Z^(-κ) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)


end

section

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (firstLogDensity)

theorem initial_density_elementary_squared_mass {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : ActualEisensteinCubic.O) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V₁ V₂ : ℝ → ℂ)
    (X lengthScale K A Vmax : ℝ) (J : ℕ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J) ≤
      (initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3)*K*(X*lengthScale)^2 := by
  let C := initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3
  have hI : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hC : 0 ≤ C := mul_nonneg (initialElementaryConstant_nonneg A Vmax) (pow_nonneg hI _)
  have hd := childDensity_elementary_all_scales p hp hcop hg hc hinj pool Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m T V₁ V₂ X lengthScale K A Vmax J hX hL hK hA hVmax hV₁ hV₂ hs₁ hs₂ hT
  change _/(X*lengthScale) ≤ C*K*X at hd
  have hraw := (div_le_iff₀ (mul_pos hX (zero_lt_one.trans_le hL))).mp hd
  have hbase : 0 ≤ (C*K*X)*(X*lengthScale) := by positivity
  calc
    _ ≤ (C*K*X)*(X*lengthScale) := hraw
    _ ≤ ((C*K*X)*(X*lengthScale))*lengthScale := le_mul_of_one_le_right hbase hL
    _ = _ := by dsimp only [C]; ring

end


section

open scoped BigOperators Classical
open SecondPassArithmetic

theorem initial_log_harmonic_small_power (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ,0 < C ∧ ∀ (Y U Kmax : ℝ),1 ≤ Y → 0 < U → 0 < Kmax → U ≤ Y → Kmax ≤ Y →
      ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) ≤ C*Y^η := by
  obtain ⟨C,hC,hbound⟩ := globalLogFactor_small_power η hη
  refine ⟨128*Real.exp 1*C,by positivity,?_⟩
  intro Y U Kmax hY hU hK hUY hKY
  let B := 1+Real.log 27+22*Real.log Y
  have hlog := Real.log_nonneg hY
  have h27 : 0 ≤ Real.log 27 := Real.log_nonneg (by norm_num)
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hu := normLogBin_le_log_upper U Y hU hUY hY
  have hk := normLogBin_le_log_upper Kmax Y hK hKY hY
  have huB : (normLogBin U : ℝ)+1 ≤ B := by dsimp [B]; linarith
  have hkB : (normLogBin Kmax : ℝ)+1 ≤ B := by dsimp [B]; linarith
  have hcard : ((secondLogBinBox U Kmax).card : ℝ) ≤ B^3 := by
    rw [secondLogBinBox_card,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ B^2*B := mul_le_mul (pow_le_pow_left₀ (by positivity) huB 2) hkB (by positivity) (sq_nonneg B)
      _ = _ := by ring
  have hh : 128*Real.exp 1*(normLogBin U+1 : ℝ) ≤ 128*Real.exp 1*B :=
    mul_le_mul_of_nonneg_left huB (by positivity)
  calc
    _ ≤ B^3*(128*Real.exp 1*B) := mul_le_mul hcard hh (by positivity) (pow_nonneg (zero_le_one.trans hB) _)
    _ = 128*Real.exp 1*B^4 := by ring
    _ ≤ 128*Real.exp 1*B^10 := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hB (by decide)) (by positivity)
    _ ≤ 128*Real.exp 1*(C*Y^η) := mul_le_mul_of_nonneg_left (hbound Y hY) (by positivity)
    _ = _ := by ring

theorem initial_row_log_budget (η Ccap : ℝ) (hη : 0 < η) (hcap : 1 ≤ Ccap) :
    ∃ C : ℝ,0 < C ∧ ∀ (Z U Kmax : ℝ),1 ≤ Z → 0 < U → 0 < Kmax →
      U ≤ Ccap*Z^17 → Kmax ≤ Ccap*Z^17 →
      (Kmax*Real.exp 2)^η*((secondLogBinBox U Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin U+1 : ℝ)) ≤ C*Z^(34*η) := by
  obtain ⟨C,hC,hlog⟩ := initial_log_harmonic_small_power η hη
  refine ⟨C*(Real.exp 2)^η*Ccap^(2*η),by positivity,?_⟩
  intro Z U Kmax hZ hU hK hUY hKY
  have hZ0 := zero_lt_one.trans_le hZ
  have hcap0 := zero_lt_one.trans_le hcap
  let Y := Ccap*Z^17
  have hY : 1 ≤ Y := one_le_mul_of_one_le_of_one_le hcap (one_le_pow₀ hZ)
  have hlogs := hlog Y U Kmax hY hU hK hUY hKY
  have hrow : (Kmax*Real.exp 2)^η ≤ (Y*Real.exp 2)^η := Real.rpow_le_rpow
    (mul_pos hK (Real.exp_pos _)).le (mul_le_mul_of_nonneg_right hKY (Real.exp_pos _).le) hη.le
  calc
    _ = (Kmax*Real.exp 2)^η*(((secondLogBinBox U Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin U+1 : ℝ))) := by ring
    _ ≤ (Y*Real.exp 2)^η*(C*Y^η) := mul_le_mul hrow hlogs (by positivity) (by positivity)
    _ = C*(Real.exp 2)^η*Y^(2*η) := by
      rw [Real.mul_rpow (zero_le_one.trans hY) (Real.exp_pos _).le]
      rw [show 2*η=η+η by ring,Real.rpow_add (zero_lt_one.trans_le hY)]
      ring
    _ = (C*(Real.exp 2)^η*Ccap^(2*η))*Z^(34*η) := by
      dsimp [Y]
      rw [Real.mul_rpow hcap0.le (pow_nonneg hZ0.le _),←Real.rpow_natCast_mul hZ0.le]
      norm_num
      ring_nf

end


end InitialMeanSquare

end

end OAI

end



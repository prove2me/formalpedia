-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0066
-- name    : PNT_ZeroFree_433_0066
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T16:40:05.563929+00:00
-- url     : https://prove2.me/theorems/7a4f3f5e-c568-4cb8-9de7-dc31488b73dd
-- title:
--   Zero-free region foundations: CubicSieve.KernelEnergy [0066]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.KernelEnergy
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/KernelEnergy.lean#L84-L751

import Definitions.Def_PNT_ZeroFree_433_0065

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/KernelEnergy.lean#L84-L751
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.KernelEnergy
section
namespace OAI

noncomputable section

namespace FirstPassCubeLabels

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

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

def actualFirstKernel {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ lengthScale : ℝ) (d h : O) : ℂ :=
  ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
    (V₁ (columnLog p X₁ N) * V₂ (columnLog p X₂ P)) *
    ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
    paperRadialFourier W (lengthScale * ‖eisEmbedding h‖ ^ 2 /
      (‖eisEmbedding d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂))) *
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0

def firstColumnEnergy {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (d h : O) (b : 𝓢(ℝ, ℂ)) : ℝ :=
  ∫ t : ℝ, ‖b t‖ * ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ *
    rayIdealEnergy p hg F
      (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
        (normalizedColumn p C) V (columnLog p X) t d) negative h

theorem firstColumnEnergy_nonneg {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (d h : O) (b : 𝓢(ℝ, ℂ)) :
    0 ≤ firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ negative C V X d h b := by
  apply integral_nonneg
  intro t
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (rayIdealEnergy_nonneg _ _ _ _ _ _)

theorem actual_first_kernel_energy_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale → ∀ d h : O, d ≠ 0 → h ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ K ∧
        ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h‖ ≤
        (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ d h b) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ d h b) := by
  obtain ⟨K, hK, hs⟩ := actual_first_kernel_to_ideal_rows p hp hinj hcop hg hc hpr F B hFB
    v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ hX₁ hX₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro lengthScale hL d h hd hh
  obtain ⟨b, hi, hb, _, he⟩ := hs lengthScale hL d h hd hh
  refine ⟨b, hi, hb, ?_⟩
  let D₁ := fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ true
    (normalizedColumn p C₁) V₁ (columnLog p X₁) t d
  let D₂ := fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ false
    (normalizedColumn p C₂) V₂ (columnLog p X₂) t d
  have hiE := cube_integral_norm_le_energy p hg F D₁ D₂
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ true _ _ _ d)
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ false _ _ _ d)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ true _ _ _ t d S)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ false _ _ _ t d S)
    h b (cubeBaseFactor p hp hg B v ε₁ ε₂ d h)
  change actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h = _ at he
  rw [he, norm_mul]
  have hn : ‖(lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)‖ =
      lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ := by
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL.le,
      abs_of_nonneg (norm_nonneg _)]
  rw [hn, mul_assoc]
  exact mul_le_mul_of_nonneg_left hiE (div_nonneg hL.le (norm_nonneg _))

end

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportRay supportConjugateSum)
open RayFourExpansion (RayCharacter)

section Local
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i)

theorem row_union (S T : Finset ι) (hd : Disjoint S T) (a : O) :
    finiteSquarefreeRow P hg (S ∪ T) a =
      finiteSquarefreeRow P hg S a * finiteSquarefreeRow P hg T a := by
  exact Finset.prod_union hd

include hg in
theorem mask_union (S T : Finset ι) (hd : Disjoint S T) (a : O) :
    rowCoprimeMask P (S ∪ T) a = rowCoprimeMask P S a * rowCoprimeMask P T a := by
  simp only [← row_sixth P hg, row_union P hg S T hd, mul_pow]

omit [DecidableEq ι] in
theorem row_four_star (S : Finset ι) (f h : O) :
    finiteSquarefreeRow P hg S f ^ 4 * star (finiteSquarefreeRow P hg S h) =
      star (finiteSquarefreeRow P hg S (h * f ^ 2)) := by
  have hf : star (finiteSquarefreeRow P hg S (f ^ 2)) =
      finiteSquarefreeRow P hg S f ^ 4 := by
    rw [row_pow, star_pow, finiteSquarefreeRow_conj_as_row_label]
    calc
      _ = finiteSquarefreeRow P hg S f ^ 4 * finiteSquarefreeRow P hg S f ^ 6 := by ring
      _ = _ := by
        rw [row_sixth]
        simpa only [pow_one] using row_power_mul_mask_power P hg S f 4 1 (by decide)
  rw [finiteSquarefreeRow_mul, star_mul, hf]

def beforeDilationLabel {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (side : Bool) (c d f : O) (S : Finset ι) : ℂ :=
  finiteSquarefreeRow P hg S c ^ 4 * finiteSquarefreeRow P hg S d *
    (rowCoprimeMask P S (cubeRadical p B) *
      finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side)) *
    finiteSquarefreeRow P hg S f ^ 4

def afterDilationLabel {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (c d : O) (S : Finset ι) : ℂ :=
  finiteSquarefreeRow P hg S (c * jLabel p B v ε₁ ε₂) ^ 4 *
    finiteSquarefreeRow P hg S d * rowCoprimeMask P S (b0Label p B v ε₁ ε₂)

theorem beforeDilationLabel_union {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (side : Bool) (c d f : O)
    (S T : Finset ι) (hd : Disjoint S T) :
    beforeDilationLabel P hg p B v ε₁ ε₂ side c d f (S ∪ T) =
      beforeDilationLabel P hg p B v ε₁ ε₂ side c d f S *
      beforeDilationLabel P hg p B v ε₁ ε₂ side c d f T := by
  simp only [beforeDilationLabel, row_union P hg S T hd, mask_union P hg S T hd, mul_pow]
  ring

omit [DecidableEq ι] in
theorem beforeDilationLabel_norm_le_one {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (side : Bool) (c d f : O) (S : Finset ι) :
    ‖beforeDilationLabel P hg p B v ε₁ ε₂ side c d f S‖ ≤ 1 := by
  have hm : ‖rowCoprimeMask P S (cubeRadical p B)‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  simp only [beforeDilationLabel, norm_mul, norm_pow]
  calc
    _ ≤ (1:ℝ)^4 * 1 * (1 * 1^4 * 1) * 1^4 := by
      gcongr <;> first | exact hm | exact finiteSquarefreeRow_norm_le_one P hg S _
    _ = 1 := by norm_num

omit [DecidableEq ι] in
theorem beforeDilationLabel_star_row {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (side : Bool) (c d f h : O) (S : Finset ι) :
    beforeDilationLabel P hg p B v ε₁ ε₂ side c d f S *
      star (finiteSquarefreeRow P hg S h) =
    afterDilationLabel P hg p B v ε₁ ε₂ c d S *
      star (finiteSquarefreeRow P hg S (h * f^2 * dilationLabel p B v ε₁ ε₂)) := by
  unfold beforeDilationLabel afterDilationLabel
  calc
    _ = (finiteSquarefreeRow P hg S c ^ 4 * finiteSquarefreeRow P hg S d) *
      ((rowCoprimeMask P S (cubeRadical p B) *
        finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
        finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side)) *
        (finiteSquarefreeRow P hg S f ^ 4 * star (finiteSquarefreeRow P hg S h))) := by ring
    _ = _ := by
      rw [row_four_star, first_pass_after_dual_dilation P hg S p B v ε₁ ε₂ hv side]
      simp only [finiteSquarefreeRow_mul, mul_pow]
      ring
end Local

theorem rayIdealRow_eq_supportRow {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D : Finset ι)
    (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter) (h : O) :
    rayIdealRow p hg F C negative χ D h =
    supportConjugateSum (fun i => Ideal.span {p i}) hg (F \ D)
      (fun U => (if negative then star (supportRay p χ U) else supportRay p χ U) * C (D ∪ U)) h := by
  symm
  exact FirstCauchyArithmetic.supportConjugateSum_eq_conjugateIdealRowSum
    (fun i => Ideal.span {p i}) hinj hg (F \ D) _ h

def dilatedRayColumn {ι κ : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F D : Finset ι) (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter)
    (q : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (c d y : O) : ℂ :=
  supportConjugateSum (fun i => Ideal.span {p i}) hg (F \ D)
    (fun U => (if negative then star (supportRay p χ U) else supportRay p χ U) *
      C (D ∪ U) * afterDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ c d U) y

theorem rayIdealRow_beforeDilation {ι κ : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D : Finset ι)
    (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter)
    (q : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (side : Bool) (c d f h : O) :
    rayIdealRow p hg F
      (fun S => C S * beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f S)
      negative χ D h =
    beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f D *
      dilatedRayColumn p hg F D C negative χ q B v ε₁ ε₂ c d
        (h * f ^ 2 * dilationLabel q B v ε₁ ε₂) := by
  rw [rayIdealRow_eq_supportRow p hinj]
  unfold dilatedRayColumn supportConjugateSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hd : Disjoint D U := by
    exact Finset.disjoint_left.mpr (fun i hiD hiU =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hiU)).2 hiD)
  dsimp only
  rw [beforeDilationLabel_union _ hg q B v ε₁ ε₂ side c d f D U hd]
  calc
    _ = beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f D *
      supportMobius (fun i => Ideal.span {p i}) U *
      ((if negative then star (supportRay p χ U) else supportRay p χ U) * C (D ∪ U)) *
      (beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f U *
        star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U h)) := by ring
    _ = _ := by
      rw [beforeDilationLabel_star_row _ hg q B v ε₁ ε₂ hv side c d f h U]
      ring

def originalLabelColumn {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (B : Finset ι) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (c f : O) (S : Finset ι) : ℂ :=
  C S * rowCoprimeMask (fun i => Ideal.span {p i}) S (cubeRadical p B) *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S
      (aLabel p B (if negative then ε₂ else ε₁) * c) ^ 4 *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S f ^ 4

def cubeCoreCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  if negative then
    star (fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S) *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1)) *
      MixedCrossSeparation.columnG p hp hcop hg S * C S *
      star (V (y S) * FourierBridge.logPhase t (-(y S)))
  else
    fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S *
      MixedCrossSeparation.columnG p hp hcop hg S * C S *
      (V (y S) * FourierBridge.logPhase t (-(y S)))

theorem cubeLogCoefficient_originalLabel {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (c d f : O) (S : Finset ι) :
    cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d S =
    cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S *
      beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f S := by
  cases negative <;>
    simp only [cubeLogCoefficient, cubeCoreCoefficient, cubeMinusCoefficient,
      cubePlusCoefficient, FirstCauchyArithmetic.firstPassColumnMinus,
      FirstCauchyArithmetic.firstPassColumnPlus, logTwistMinus, logTwistPlus,
      originalLabelColumn, beforeDilationLabel, Bool.false_eq_true, ite_false, ite_true,
      finiteSquarefreeRow_mul, mul_pow] <;> ring

theorem rayIdealRow_cube_labels {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (c d f h : O) :
    rayIdealRow p hg F
      (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d) negative χ D h =
    beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D *
      dilatedRayColumn p hg F D (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t)
        negative χ p B v ε₁ ε₂ c d (h * f ^ 2 * dilationLabel p B v ε₁ ε₂) := by
  have he : cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d =
    fun S => cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S *
      beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f S := by
    funext S
    exact cubeLogCoefficient_originalLabel p hp hcop hg B v ε₁ ε₂ negative C V y t c d f S
  rw [he]
  exact rayIdealRow_beforeDilation p hinj hg F D _ negative χ p B v ε₁ ε₂ hv negative c d f h

theorem first_cube_energy_small_power (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
      (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B, 0 < v j)
      (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ) (V : ℝ → ℂ)
      (y : Finset ι → ℝ) (t : ℝ) (c d : O)
      (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      (∑ x ∈ s, ‖w x‖ * ‖rayIdealRow p hg F
        (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
          (originalLabelColumn p hg B ε₁ ε₂ negative C c (ConcretePrimeRowBridge.idealGenerator x.1))
            V y t d) negative χ D x.2‖ ^ 2) ≤
      M * K * Y ^ deltaLoss * ∑ z ∈ T,
        ‖dilatedRayColumn p hg F D (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t)
          negative χ p B v ε₁ ε₂ c d z‖ ^ 2 := by
  obtain ⟨K, hK, hpush⟩ := SquarefreeDivisorBound.first_element_energy_small_power deltaLoss hδ
  refine ⟨K, hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg F D B v ε₁ ε₂ hv negative χ C V y t c d s T w M Y hM hY hs hmap hT hnorm hw
  apply le_trans _ (hpush s T (dilationLabel p B v ε₁ ε₂) w
    (dilatedRayColumn p hg F D (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t)
      negative χ p B v ε₁ ε₂ c d) M Y hM hY hs hmap hT hnorm hw)
  apply Finset.sum_le_sum
  intro x hx
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [rayIdealRow_cube_labels p hp hinj hcop hg F D B v ε₁ ε₂ hv negative χ C V y t c d,
    norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (beforeDilationLabel_norm_le_one _ hg p B v ε₁ ε₂ negative c d
      (ConcretePrimeRowBridge.idealGenerator x.1) D)

theorem normalized_originalLabelColumn {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (B : Finset ι) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (c f : O) :
    normalizedColumn p (originalLabelColumn p hg B ε₁ ε₂ negative C c f) =
      originalLabelColumn p hg B ε₁ ε₂ negative (normalizedColumn p C) c f := by
  funext S
  simp only [normalizedColumn, originalLabelColumn, div_eq_mul_inv]
  ring

theorem firstColumnEnergy_original_labels {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (c d f h : O) (b : 𝓢(ℝ, ℂ)) :
    firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V X d h b =
    ∫ t : ℝ, ‖b t‖ * ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ *
      ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
        ‖rayPairWeight p r D h‖ *
        (‖beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D‖ ^ 2 *
          ‖dilatedRayColumn p hg F D
            (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative
              (normalizedColumn p C) V (columnLog p X) t)
            negative (if negative then r.1 else r.2) p B v ε₁ ε₂ c d
            (h * f ^ 2 * dilationLabel p B v ε₁ ε₂)‖ ^ 2) := by
  unfold firstColumnEnergy
  rw [normalized_originalLabelColumn]
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  unfold rayIdealEnergy
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro D hD
  rw [rayIdealRow_cube_labels p hp hinj hcop hg F D B v ε₁ ε₂ hv negative _
    (normalizedColumn p C) V (columnLog p X) t c d f h, norm_mul, mul_pow]

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

def firstDivisorWeight {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (E : Finset ι) : ℂ :=
  (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
    (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)

theorem retained_first_kernel_energy_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale →
      ∀ (Ω : Finset (Finset ι × O)) (w : Finset ι × O → ℂ),
      (∀ x ∈ Ω, x.2 ≠ 0) → ∃ b : (Finset ι × O) → 𝓢(ℝ, ℂ),
      (∀ x ∈ Ω, Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b x t‖) volume ∧
        (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂
          (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2) ^ A *
            (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b x t‖) ≤ K) ∧
      ‖∑ x ∈ Ω, (w x * firstDivisorWeight p x.1) *
        actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale
          (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
        Real.sqrt (∑ x ∈ Ω, ‖w x * firstDivisorWeight p x.1‖ *
          firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁
            (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2 (b x)) *
        Real.sqrt (∑ x ∈ Ω, ‖w x * firstDivisorWeight p x.1‖ *
          firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂
            (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2 (b x)) := by
  obtain ⟨K, hK, hs⟩ := actual_first_kernel_energy_bound p hp hinj hcop hg hc hpr F B hFB
    v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ hX₁ hX₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro lengthScale hL Ω w hΩ
  let d := fun x : Finset ι × O => primeSubsetGenerator (fun i => Ideal.span {p i}) x.1
  have hfam : ∀ x : Finset ι × O, ∃ b : 𝓢(ℝ, ℂ), x ∈ Ω →
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
      (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ (d x) x.2) ^ A *
        (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ K ∧
      ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale (d x) x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
        Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ (d x) x.2 b) *
        Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ (d x) x.2 b) := by
    intro x
    by_cases hx : x ∈ Ω
    · obtain ⟨b, hb⟩ := hs lengthScale hL (d x) x.2 (primeSubsetGenerator_ne_zero _ _) (hΩ x hx)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun hx' => (hx hx').elim⟩
  choose b hb using hfam
  refine ⟨b, fun x hx => ⟨(hb x hx).1, (hb x hx).2.1⟩, ?_⟩
  let U := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ (d x) x.2 (b x)
  let V := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ (d x) x.2 (b x)
  let a := fun x => ‖w x * firstDivisorWeight p x.1‖
  let q := lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖
  have hq : 0 ≤ q := div_nonneg hL.le (norm_nonneg _)
  have hU (x) : 0 ≤ U x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ _ _ _
  have hV (x) : 0 ≤ V x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ _ _ _
  have hterm (x) : a x * (Real.sqrt (U x) * Real.sqrt (V x)) =
      Real.sqrt (a x * U x) * Real.sqrt (a x * V x) := by
    rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_mul (norm_nonneg _)]
    calc
      _ = (Real.sqrt (a x)) ^ 2 * (Real.sqrt (U x) * Real.sqrt (V x)) := by
        rw [Real.sq_sqrt (norm_nonneg _)]
      _ = _ := by ring
  calc
    _ ≤ ∑ x ∈ Ω, ‖(w x * firstDivisorWeight p x.1) *
        actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale (d x) x.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ x ∈ Ω, q * (Real.sqrt (a x * U x) * Real.sqrt (a x * V x)) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul, ← hterm]
      calc
        _ ≤ a x * (q * Real.sqrt (U x) * Real.sqrt (V x)) :=
          mul_le_mul_of_nonneg_left (hb x hx).2.2 (norm_nonneg _)
        _ = _ := by ring
    _ = q * (∑ x ∈ Ω, Real.sqrt (a x * U x) * Real.sqrt (a x * V x)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ q * (Real.sqrt (∑ x ∈ Ω, a x * U x) * Real.sqrt (∑ x ∈ Ω, a x * V x)) :=
      mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le Ω
        (fun x => mul_nonneg (norm_nonneg _) (hU x))
        (fun x => mul_nonneg (norm_nonneg _) (hV x))) hq
    _ = _ := (mul_assoc _ _ _).symm

end

section
open scoped BigOperators Classical
open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)

theorem blockRow_norm_le_one {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (S : Finset ι) (e : ι → ℕ) (a : O) : ‖blockRow p hg S e a‖ ≤ 1 := by
  rw [blockRow_eq_product, norm_prod]
  calc
    _ ≤ ∏ i ∈ S, (1 : ℝ) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro i hi
      let : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
      exact FiniteRayExpansion.norm_char_le_one _ _
    _ = 1 := by simp

theorem cubeBaseFactor_norm_le_one {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (d h : O) :
    ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ ≤ 1 := by
  have he : ∀ i ∈ cubeActiveSupport B v ε₁ ε₂,
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val ≠ 0 := by
    intro i hi
    exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hi).2
  simp only [cubeBaseFactor, norm_mul, norm_star,
    gaussBlock_norm_one p hp hcop hg hc _ _ he (fun _ _ => ZMod.val_lt _), one_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (blockRow_norm_le_one p hg _ _ _)).trans (blockRow_norm_le_one p hg _ _ _)

theorem rayPairWeight_norm_le {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (r : RayCharacter × RayCharacter) (D : Finset ι) (h : O) :
    ‖rayPairWeight p r D h‖ ≤ ‖crossCoeff r.1 r.2‖ := by
  rw [norm_rayPairWeight p hinj hc]
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) D h‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  exact mul_le_of_le_one_right (norm_nonneg _) hm

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FourierBridge (logPhase)

def firstLogDensity (J : ℕ) (t : ℝ) : ℝ := ((1 + ‖t‖) ^ (J + 2))⁻¹

theorem firstLogDensity_nonneg (J : ℕ) (t : ℝ) : 0 ≤ firstLogDensity J t := by
  unfold firstLogDensity
  positivity

theorem firstLogDensity_integrable (J : ℕ) : Integrable (firstLogDensity J) volume := by
  have h := integrable_one_add_norm (E := ℝ) («μ» := (volume : Measure ℝ))
    (r := (J + 2 : ℕ)) (by norm_num; linarith [Nat.cast_nonneg (α := ℝ) J])
  convert! h using 1
  funext t
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  rfl

theorem firstLogDensity_moment_integrable (J : ℕ) :
    Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * firstLogDensity J t) volume := by
  convert! firstLogDensity_integrable 0 using 1
  funext t
  have ht : 1 + ‖t‖ ≠ 0 := ne_of_gt (by positivity)
  simp only [firstLogDensity, zero_add, pow_add, mul_inv_rev]
  field_simp

theorem two_variable_radial_envelope (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ x y : ℝ, V₁ x * V₂ y * paperRadialFourier W (R * Real.exp (-x-y)) =
        ∫ t : ℝ, (V₁ x * logPhase t (-x)) * (V₂ y * logPhase t (-y)) * b t) ∧
      (∀ t : ℝ, (1 + R) ^ A * ‖b t‖ ≤ K * firstLogDensity J t) := by
  let V : Bool → ℝ → ℂ := fun j => if j then V₂ else V₁
  let M : Bool → ℝ := fun j => if j then M₂ else M₁
  have hM : ∀ j, 0 ≤ M j := by intro j; cases j <;> assumption
  have hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j := by
    intro j; cases j
    · exact hV₁
    · exact hV₂
  obtain ⟨K, hK, hsep⟩ := EisensteinSchwartzPoisson.paperRadialFourier_log_separation_envelope
    W V (fun _ => -1) M hM hV A (J + 2)
  refine ⟨K, hK, ?_⟩
  intro R hR
  obtain ⟨b, hb, _, _, hpoint⟩ := hsep R hR
  refine ⟨b, ?_, ?_⟩
  · intro x y
    have hs := hb (fun j => if j then y else x)
    simpa only [V, Fintype.prod_bool, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
      neg_one_mul, mul_neg_one, sub_eq_add_neg, add_comm, mul_comm, mul_left_comm, mul_assoc] using hs
  · intro t
    rw [firstLogDensity, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖t‖) (J + 2))).mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hpoint t

theorem actualFirstKernel_eq_separated {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (lengthScale : ℝ) (d h : O) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ x y : ℝ, V₁ x * V₂ y * paperRadialFourier W
      (firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h * Real.exp (-x-y)) =
      ∫ t : ℝ, (V₁ x * logPhase t (-x)) * (V₂ y * logPhase t (-y)) * b t) :
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h =
    ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
      ∫ t : ℝ, b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
        idealPairReindex p hg F
          (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ true
            (normalizedColumn p C₁) V₁ (columnLog p X₁) t d)
          (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ false
            (normalizedColumn p C₂) V₂ (columnLog p X₂) t d) h := by
  have hs := cube_integral_of_radial_separation p hp hinj hcop hg hc hpr F B hFB
    v ε₁ ε₂ (normalizedColumn p C₁) (normalizedColumn p C₂) d h W V₁ V₂
    (columnLog p X₁) (columnLog p X₂)
    (firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) b hsep
  simp only [cubeLogCoefficient, Bool.false_eq_true, ite_false, ite_true]
  rw [← hs.2]
  unfold actualFirstKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP : Disjoint N P
  · rw [if_pos hNP, if_pos hNP]
    have hNB := hFB.mono_left (Finset.mem_powerset.mp hN)
    have hPB := hFB.mono_left (Finset.mem_powerset.mp hP)
    rw [actual_radial_argument p hp N P (cubeActiveSupport B v ε₁ ε₂) hNP
      (hNB.mono_right (Finset.filter_subset _ _))
      (hPB.mono_right (Finset.filter_subset _ _)) lengthScale X₁ X₂ hX₁ hX₂ d h]
    have hpre := actual_pair_prefactor p hp hcop hg N P B hNP hNB hPB v ε₁ ε₂ C₁ C₂ lengthScale d h
    calc
      _ = (V₁ (columnLog p X₁ N) * V₂ (columnLog p X₂ P) *
          paperRadialFourier W (lengthScale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)))) *
          (((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
            threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h) := by ring
      _ = _ := by rw [hpre]; ring
  · simp [hNP]

theorem actual_first_kernel_energy_envelope {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale → ∀ d h : O, d ≠ 0 → h ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ t : ℝ, (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) ^ A *
          ‖b t‖ ≤ K * firstLogDensity J t) ∧
        ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h‖ ≤
        (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ d h b) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ d h b) := by
  obtain ⟨K, hK, hs⟩ := two_variable_radial_envelope W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro lengthScale hL d h hd hh
  have hR : 0 < firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h := by
    unfold firstDualScale
    exact div_pos (mul_pos hL (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)) 2))
      (mul_pos (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd)) 2)
        (primeProductNorm_pos p hp _)) hX₁) hX₂)
  obtain ⟨b, hsep, hb⟩ := hs _ hR
  refine ⟨b, hb, ?_⟩
  rw [actualFirstKernel_eq_separated p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂
    C₁ C₂ W V₁ V₂ X₁ X₂ hX₁ hX₂ lengthScale d h b hsep, norm_mul]
  have hi := cube_integral_norm_le_energy p hg F
    (fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ true
      (normalizedColumn p C₁) V₁ (columnLog p X₁) t d)
    (fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ false
      (normalizedColumn p C₂) V₂ (columnLog p X₂) t d)
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ true _ _ _ d)
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ false _ _ _ d)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ true _ _ _ t d S)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ false _ _ _ t d S)
    h b (cubeBaseFactor p hp hg B v ε₁ ε₂ d h)
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL.le,
    abs_of_nonneg (norm_nonneg _)]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hi (div_nonneg hL.le (norm_nonneg _))

end FirstPassCubeLabels

end

end OAI

end



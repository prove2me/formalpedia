-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0141_parallel1
-- name    : PNT_ZeroFree_433_0141_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:48:02.530395+00:00
-- url     : https://prove2.me/theorems/bc82c93a-d545-423b-9cfb-abf83fa54026
-- title:
--   Zero-free region foundations: CubicSieve.LiteralSources [0141_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.LiteralSources
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/LiteralSources.lean#L170-L649

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0049
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0079
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0087
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0095
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0100
import Definitions.Def_PNT_ZeroFree_433_0102
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0118_parallel1
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1
import Definitions.Def_PNT_ZeroFree_433_0122_parallel1
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0127_parallel2
import Definitions.Def_PNT_ZeroFree_433_0128_parallel1
import Definitions.Def_PNT_ZeroFree_433_0129_parallel1
import Definitions.Def_PNT_ZeroFree_433_0133_parallel1
import Definitions.Def_PNT_ZeroFree_433_0135_parallel1
import Definitions.Def_PNT_ZeroFree_433_0137_parallel2
import Definitions.Def_PNT_ZeroFree_433_0181_parallel1
import Definitions.Def_PNT_ZeroFree_433_0208_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/LiteralSources.lean
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

open scoped BigOperators Classical SchwartzMap ContDiff


namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise

local notation "O" => ActualEisensteinCubic.O

lemma complex_norm_mul_add_sq (a b c d : ℂ) :
    ‖a*c+b*d‖^2≤(‖a‖^2+‖b‖^2)*(‖c‖^2+‖d‖^2) := by
  have ht : ‖a*c+b*d‖≤‖a‖*‖c‖+‖b‖*‖d‖ := by simpa only [norm_mul] using norm_add_le (a*c) (b*d)
  have hs := pow_le_pow_left₀ (norm_nonneg (a*c+b*d)) ht 2
  nlinarith only [hs,sq_nonneg (‖a‖*‖d‖-‖b‖*‖c‖)]

lemma matrixFrobenius_nonneg (g : SL(2,ℂ)) : 0≤matrixFrobenius g := by
  unfold matrixFrobenius rowEnergy
  positivity

lemma matrixFrobenius_mul_le (g h : SL(2,ℂ)) :
    matrixFrobenius (g*h)≤matrixFrobenius g*matrixFrobenius h := by
  have hb (i j : Fin 2) := complex_norm_mul_add_sq (g i 0) (g i 1) (h 0 j) (h 1 j)
  simp only [matrixFrobenius,rowEnergy,complexMatrixRow,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two]
  nlinarith only [hb 0 0,hb 0 1,hb 1 0,hb 1 1]

lemma matrixFrobenius_inv (g : SL(2,ℂ)) : matrixFrobenius g⁻¹=matrixFrobenius g := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp only [matrixFrobenius,rowEnergy,complexMatrixRow]
  change ‖g 1 1‖^2+‖-g 0 1‖^2+(‖-g 1 0‖^2+‖g 0 0‖^2)=_
  simp only [norm_neg]
  ring

lemma hyperbolicFrobenius_nonneg (w : HyperbolicSpace) : 0≤hyperbolicFrobenius w := by
  induction w using Quotient.inductionOn with
  | _ g => exact matrixFrobenius_nonneg g

lemma matrixFrobenius_le_displacement (g : SL(2,ℂ)) (w : HyperbolicSpace) :
    matrixFrobenius g≤hyperbolicFrobenius (g • w)*hyperbolicFrobenius w := by
  induction w using Quotient.inductionOn with
  | _ h =>
    change matrixFrobenius g≤matrixFrobenius (g*h)*matrixFrobenius h
    have hb := matrixFrobenius_mul_le (g*h) h⁻¹
    simpa only [mul_inv_cancel_right,matrixFrobenius_inv] using hb


end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise

namespace CubicEisenstein

section
local notation "O" => ActualEisensteinCubic.O

instance upperCoordinatesLocallyCompact : LocallyCompactSpace UpperCoordinates :=
  (isOpen_lt continuous_const continuous_snd : IsOpen {p : ℂ×ℝ | 0<p.2}).locallyCompactSpace


instance upperCoordinatesPolish : PolishSpace UpperCoordinates :=
  (isOpen_lt continuous_const continuous_snd : IsOpen {p : ℂ×ℝ | 0<p.2}).polishSpace


end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal


end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label)

@[ext] structure GlobalFirstData (ι : Type*) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  common : Finset ι
  firstDivisor : Finset ι

namespace GlobalFirstData
variable {ι : Type*}
def append (b : GlobalFirstData ι) (x : SecondExpansionData ι) : GlobalSecondData ι :=
  ⟨b.cube,b.firstCommon,b.common,b.firstDivisor,x⟩
end GlobalFirstData

namespace GlobalSecondData
variable {ι : Type*}
def first (x : GlobalSecondData ι) : GlobalFirstData ι :=
  ⟨x.cube,x.firstCommon,x.common,x.firstDivisor⟩
@[simp] theorem append_first (x : GlobalSecondData ι) : x.first.append x.source=x := by cases x; rfl
@[simp] theorem first_append (b : GlobalFirstData ι) (x : SecondExpansionData ι) : (b.append x).first=b := rfl
@[simp] theorem source_append (b : GlobalFirstData ι) (x : SecondExpansionData ι) : (b.append x).source=x := rfl
end GlobalSecondData

section
variable {ι : Type*} [DecidableEq ι]

def globalFirstRawPool (pool : Finset ι) (b : GlobalFirstData ι) : Finset ι :=
  (pool\(b.cube.support∪b.common))\b.firstCommon

def globalFirstExpansionPool (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) : Finset (GlobalSecondData ι) :=
  s.biUnion (fun b => (secondExpansionPool (globalFirstRawPool pool b) (cutoff b)).image b.append)

theorem mem_globalFirstExpansionPool (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) (x : GlobalSecondData ι) :
    x∈globalFirstExpansionPool pool s cutoff ↔
      x.first∈s ∧ x.source∈secondExpansionPool (globalFirstRawPool pool x.first) (cutoff x.first) := by
  simp only [globalFirstExpansionPool,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨b,hb,z,hz,rfl⟩
    exact ⟨hb,hz⟩
  · rintro ⟨hb,hx⟩
    exact ⟨x.first,hb,x.source,hx,x.append_first⟩

theorem sum_globalFirstExpansionPool {M : Type*} [AddCommMonoid M]
    (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) (f : GlobalSecondData ι → M) :
    ∑ x∈globalFirstExpansionPool pool s cutoff,f x =
    ∑ b∈s,∑ x∈secondExpansionPool (globalFirstRawPool pool b) (cutoff b),f (b.append x) := by
  unfold globalFirstExpansionPool
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_image]
    intro x hx y hy heq
    exact congrArg GlobalSecondData.source heq
  · intro b hb c hc hne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp hy
    exact hne (congrArg GlobalSecondData.first heq).symm

end

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalFirstBlockColumnScale (ell : ℝ) (side : Bool) (b : GlobalFirstData ι) : ℝ :=
  ell/(primeProductNorm p (b.cube.sideDivisor side)*primeProductNorm p b.common)

def globalFirstBlockLabel (b : GlobalFirstData ι) : O :=
  secondBaseLabel p b.cube.support b.common b.cube.leftExponent b.cube.rightExponent b.cube.leftBit b.cube.rightBit

def globalFirstBlockBadLabel (b : GlobalFirstData ι) : O :=
  b0Label p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit

def globalFirstBlockTest (g : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (b : GlobalFirstData ι) : Finset ι → ℂ :=
  normalizedColumn p (fun A => g (columnLog p
    (globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon) A))

def globalFirstTruncatedSource
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℂ :=
  ∑ b∈s,w b*(primeProductNorm p b.firstCommon : ℂ)⁻¹*
    truncatedSecondSource p hp hg hinj (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) W (Y b) (cutoff b)


end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalFirstCoreRow (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (χ : RayCharacter)
    (r : FirstCoreIndex) (t : ℝ) (b : GlobalFirstData ι) (z : O) : ℂ :=
  firstCoreInputRow p hg (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    side χ Ψ m (normalizedColumn p (fun A => g (columnLog p (globalFirstBlockColumnScale p ell side b) A)))
    V (columnLog p (globalFirstBlockColumnScale p ell side b))
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r t z

def globalFirstCoreCorrection (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool)
    (t : ℝ) (b : GlobalFirstData ι) : ℝ :=
  ‖firstCoreTest (normalizedColumn p (fun A => g (columnLog p (globalFirstBlockColumnScale p ell side b) A)))
    V (columnLog p (globalFirstBlockColumnScale p ell side b)) side t b.firstCommon ∅‖^2

def globalFirstSourceTail (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℂ :=
  ∑ b∈s,w b*(primeProductNorm p b.firstCommon : ℂ)⁻¹*
    secondSourceTail p hp hg hinj (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) W (Y b) (cutoff b)

def globalFirstSourceZero
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℂ :=
  ∑ b∈s,w b*(primeProductNorm p b.firstCommon : ℂ)⁻¹*
    truncatedSecondZero p hg (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) W (Y b) (cutoff b)

theorem globalFirstTruncatedSource_split
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    globalFirstTruncatedSource p hp hg hinj pool s w cutoff Ψ m g W ell side Y =
      globalFirstTruncatedSource p hp hg hinj pool s w (fun b G E => (cutoff b G E).erase 0) Ψ m g W ell side Y +
      globalFirstSourceZero p hg pool s w cutoff Ψ m g W ell side Y := by
  unfold globalFirstTruncatedSource globalFirstSourceZero
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [truncatedSecondSource_eq_nonzero_add_zero]
  exact mul_add _ _ _

theorem globalFirstCoreRows_smoothed
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ,ℂ)) (ell : ℝ) (hell : 0 < ell) (side : Bool)
    (χ : RayCharacter) (r : FirstCoreIndex) (t : ℝ)
    (Y : GlobalFirstData ι → ℝ) (hY : ∀ b∈s,0 < Y b) :
    (∑ b∈s,w b*∑' z : O,W (‖eisEmbedding z‖^2/Y b)*
      (‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2 : ℝ)) =
      globalFirstTruncatedSource p hp hg hinj pool s w cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) W ell side Y +
      globalFirstSourceTail p hp hg hinj pool s w cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) W ell side Y := by
  unfold globalFirstTruncatedSource globalFirstSourceTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  have hX : 0 < globalFirstBlockColumnScale p ell side b :=
    div_pos hell (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))
  have he := firstCoreInputRow_smoothed_truncated p hp hg hinj hc
    (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    side χ Ψ m g V W (globalFirstBlockColumnScale p ell side b) hX (Y b) (hY b hb)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r t (cutoff b)
  dsimp only at he
  have he' := congrArg (fun z : ℂ => w b*z) he
  simpa only [globalFirstCoreRow,globalFirstRawPool,globalFirstBlockBadLabel,globalFirstBlockLabel,
    secondBaseLabel,globalFirstBlockTest,mul_add,mul_assoc,Complex.ofReal_inv] using he'

theorem globalFirstCoreRows_finite_le_sources
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
    (hw : ∀ b∈s,0 ≤ w b)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (hell : 0 < ell) (side : Bool)
    (χ : RayCharacter) (r : FirstCoreIndex) (t : ℝ)
    (Y : GlobalFirstData ι → ℝ) (hY : ∀ b∈s,0 < Y b)
    (T : GlobalFirstData ι → Finset O)
    (hT : ∀ b∈s,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y b)
    (hT0 : ∀ b∈s,∀ z∈T b,z ≠ 0) :
    (∑ b∈s,w b*((∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2)+
      globalFirstCoreCorrection p g V ell side t b)) ≤
      ‖globalFirstTruncatedSource p hp hg hinj pool s (fun b => w b)
        (fun b G E => (cutoff b G E).erase 0) (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ +
      ‖globalFirstSourceZero p hg pool s (fun b => w b) cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ +
      ‖globalFirstSourceTail p hp hg hinj pool s (fun b => w b) cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ := by
  have henergy : (∑ b∈s,w b*((∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2)+
      globalFirstCoreCorrection p g V ell side t b)) ≤
      (∑ b∈s,(w b : ℂ)*∑' z : O,rowMajorant (‖eisEmbedding z‖^2/Y b)*
        (‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2 : ℝ)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_le_sum
    intro b hb
    have hh := firstCoreInputRow_finite_le_corrected_source p hg
      (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
      side χ Ψ m (normalizedColumn p (fun A => g (columnLog p (globalFirstBlockColumnScale p ell side b) A)))
      V (columnLog p (globalFirstBlockColumnScale p ell side b))
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r t (T b) (Y b) (hY b hb) (hT b hb) (hT0 b hb)
    have hh' := mul_le_mul_of_nonneg_left (le_sub_iff_add_le.mp hh) (hw b hb)
    simpa only [globalFirstCoreRow,globalFirstCoreCorrection,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using hh'
  rw [globalFirstCoreRows_smoothed p hp hg hinj hc pool s (fun b => w b) cutoff Ψ m g V rowMajorant ell hell side χ r t Y hY,
    globalFirstTruncatedSource_split] at henergy
  exact henergy.trans ((Complex.re_le_norm _).trans ((norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) le_rfl)))

end SecondPassArithmetic

end

end OAI

end



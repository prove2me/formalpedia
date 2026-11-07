-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoprimeBilinearBound
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_CoprimeBilinearBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:14:07.4912+00:00
-- url     : https://prove2.me/theorems/f2cfe41d-eb83-4c3e-8f2b-bbee7d07ca7f
-- title:
--   Coprime Bilinear Bound
-- statement:
--   Definitions and structural lemmas for Coprime Bilinear Bound, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CoprimeBilinearBound.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Theorems.Thm_OAI_IdealDivisorBound_ideal_divisor_small_power

set_option autoImplicit false
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
open scoped BigOperators Classical
namespace CoprimeBilinearSieve
open FiniteSieveOperator CoprimeSieveOperator CoprimeMobiusExtension
end CoprimeBilinearSieve
namespace IdealCoprimeBilinearSieve
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum IdealCoprimeSieveOperator FiniteSieveOperator
end IdealCoprimeBilinearSieve
namespace DivisorBlockCauchy
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum FiniteSieveOperator IdealCoprimeSieveOperator
def divisorConstant (ε : ℝ) (hε : 0 < ε) : ℝ :=
  (IdealDivisorBound.ideal_divisor_small_power ε hε).choose
end DivisorBlockCauchy
namespace IdealDivisorBilinearBlocks
abbrev O := ActualEisensteinCubic.O
open FiniteSieveOperator IdealCoprimeSieveOperator DivisorBlockCauchy
def blockValue {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (left : n → Ideal O) (right : p → Ideal O)
    (A : Ideal O → Matrix m n ℂ) (B : Ideal O → Matrix m p ℂ)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) : ℝ :=
  ∑ i, ‖∑ j, ∑ k, if IsCoprime (left j) (right k) then
    star (A D i j * (if D ∣ left j then a j else 0)) *
      (B E i k * (if E ∣ right k then b k else 0)) else 0‖
end IdealDivisorBilinearBlocks
namespace FiniteSieveRestriction
open FiniteSieveOperator
variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
def extendByZero (S : Finset n) (f : n → p) (u : n → ℂ) (k : p) : ℂ :=
  ∑ j ∈ S, if f j = k then u j else 0
end FiniteSieveRestriction
open scoped BigOperators
namespace FiniteSieveOperator
end FiniteSieveOperator
open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
abbrev O := ActualEisensteinCubic.O
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss
def Admissible (I : Ideal O) : Prop :=
  I ≠ 0 ∧ Squarefree I ∧ ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
    lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2
theorem singletonPositive (I : Ideal O) (h : Admissible I) : ∀ J ∈ ({I} : Finset (Ideal O)), J ≠ ⊥ := by
  intro J hJ
  rcases Finset.mem_singleton.mp hJ with rfl
  exact h.1
theorem singletonGood (I : Ideal O) (h : Admissible I) :
    ∀ J ∈ ({I} : Finset (Ideal O)), ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors J,
      goodLambda ∉ P := by
  intro J hJ P hP
  rcases Finset.mem_singleton.mp hJ with rfl
  exact (h.2.2 P hP).1
def quadraticRow (I : Ideal O) (z : O) : ℂ :=
  if h : Admissible I then
    (idealSexticRow {I} (singletonPositive I h) (singletonGood I h) I z) ^ 3
  else 0
def idealRange (X : ℝ) : Finset (Ideal O) := (idealsUpTo ⌊X⌋₊).filter Admissible
theorem mem_idealRange {X : ℝ} {I : Ideal O} :
    I ∈ idealRange X ↔ Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
  rw [idealRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, ha⟩
    refine ⟨ha, ?_⟩
    have hX : 0 ≤ X := by
      by_contra hn
      have hz : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hX)
  · rintro ⟨ha, hN⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun h => ha.1 (Ideal.absNorm_eq_zero_iff.mp h)),
      Nat.le_floor hN⟩, ha⟩
theorem idealRange_mono {X Y : ℝ} (h : X ≤ Y) : idealRange X ⊆ idealRange Y := by
  intro I hI
  rcases mem_idealRange.mp hI with ⟨ha, hN⟩
  exact mem_idealRange.mpr ⟨ha, hN.trans h⟩
def matrix (M N : ℝ) : Matrix (idealRange M) (idealRange N) ℂ :=
  fun I J => quadraticRow J.val (primaryGenerator I.val)
def sieveNorm (M N : ℝ) : ℝ := ‖FiniteSieveOperator.operator (matrix M N)‖ ^ 2
def rangeInclusion {X Y : ℝ} (h : X ≤ Y) (I : idealRange X) : idealRange Y :=
  ⟨I.val, idealRange_mono h I.property⟩
end CanonicalQuadraticSieve
end
end OAI



-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_CubicJacobi
-- name    : OAI_NumberTheory_DirichletL_Reciprocity_CubicJacobi
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:08:19.342339+00:00
-- url     : https://prove2.me/theorems/a38d4ef9-d2a6-4dd3-a1b1-5e5cab5bab1f
-- title:
--   Cubic Jacobi
-- statement:
--   Definitions and structural lemmas for Cubic Jacobi, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Reciprocity/CubicJacobi.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_IdealMobius
import Theorems.Thm_OAI_ActualEisensteinCoordinates_unique_coordinates
import Theorems.Thm_OAI_ActualEisensteinCubic_omega_sq_for_norm
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_ActualEisensteinCubic_qNat_eq_absNorm_span
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_ShortDraftLatticeCount_coords_eval
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk


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
namespace CubicJacobiGlobal
abbrev O := ActualEisensteinCubic.O
abbrev K := ActualEisensteinCubic.K
open ActualEisensteinCubic CompletedGauss
def primeValue (P : Ideal O) (x : O) : O :=
  if h : P.IsMaximal ∧ lambda ∉ P then
    letI : P.IsMaximal := h.1
    cubicChar P h.2 (Ideal.Quotient.mk P x)
  else 0
@[simp] theorem primeValue_eq (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (x : O) :
    primeValue P x = cubicChar P hgood (Ideal.Quotient.mk P x) := by
  simp only [primeValue, dif_pos (show P.IsMaximal ∧ lambda ∉ P from
    ⟨inferInstance, hgood⟩)]
def idealSymbol (I : Ideal O) (x : O) : O :=
  if I = 0 then 0 else
    ((UniqueFactorizationMonoid.normalizedFactors I).map (fun P => primeValue P x)).prod
@[simp] theorem idealSymbol_zero (x : O) : idealSymbol 0 x = 0 := by simp [idealSymbol]
@[simp] theorem idealSymbol_bot (x : O) : idealSymbol ⊥ x = 0 := idealSymbol_zero x
@[simp] theorem idealSymbol_one (x : O) : idealSymbol 1 x = 1 := by
  rw [idealSymbol, if_neg one_ne_zero, UniqueFactorizationMonoid.normalizedFactors_one]
  rfl
@[simp] theorem idealSymbol_top (x : O) : idealSymbol ⊤ x = 1 := by
  simpa only [Ideal.one_eq_top] using idealSymbol_one x
def symbol (x y : O) : O := idealSymbol (Ideal.span {y}) x
@[simp] theorem symbol_one (x : O) : symbol x 1 = 1 := by simp [symbol]
@[simp] theorem symbol_zero (x : O) : symbol x 0 = 0 := by simp [symbol]
end CubicJacobiGlobal
namespace CubicRamified
abbrev O := ActualEisensteinCubic.O
abbrev K := ActualEisensteinCubic.K
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss
lemma lambda_def : lambda = omega - 1 := rfl
def sevenPrime : O := 1 + 3 * omega
def sevenIdeal : Ideal O := Ideal.span {sevenPrime}
theorem sevenPrime_norm : ShortDraftLatticeCount.qNat sevenPrime = 7 := by
  change ShortDraftLatticeCount.qNat (ActualEisensteinCoordinates.eval 1 3) = 7
  unfold ShortDraftLatticeCount.qNat
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q]
  rfl
theorem sevenPrime_ne_zero : sevenPrime ≠ 0 := by
  intro hz
  change ActualEisensteinCoordinates.eval 1 3 = 0 at hz
  have hh : ActualEisensteinCoordinates.eval 1 3 =
      ActualEisensteinCoordinates.eval 0 0 :=
    hz.trans (by simp [ActualEisensteinCoordinates.eval])
  have h := (ActualEisensteinCoordinates.unique_coordinates hh).1
  norm_num at h
theorem sevenIdeal_norm : Ideal.absNorm sevenIdeal = 7 := by
  rw [sevenIdeal, ← qNat_eq_absNorm_span, sevenPrime_norm]
instance sevenIdeal_isMaximal : sevenIdeal.IsMaximal := by
  have hp : sevenIdeal.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by
    rw [sevenIdeal_norm, Nat.irreducible_iff_nat_prime]
    decide)
  exact hp.isMaximal (Ideal.span_singleton_eq_bot.not.mpr sevenPrime_ne_zero)
theorem sevenPrime_primary : lambda ^ 2 ∣ sevenPrime - 1 := by
  refine ⟨-1, ?_⟩
  rw [lambda_def]
  dsimp [sevenPrime]
  linear_combination omega_sq_for_norm
theorem sevenIdeal_good : lambda ∉ sevenIdeal :=
  primary_maximal_divisor_good sevenPrime sevenPrime_primary sevenIdeal
    (Ideal.subset_span (by simp []))
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss
def primaryCoord (A B : ℤ) : O := ActualEisensteinCoordinates.eval (1 + 3 * A) (3 * B)
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss
end CubicRamified
end
end OAI



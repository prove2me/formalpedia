-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0271_parallel1_1
-- name    : PNT_ZeroFree_433_0271_parallel1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:48:44.44159+00:00
-- url     : https://prove2.me/theorems/e6e337b7-c3d5-482b-9c3b-5b73ab0c24bb
-- title:
--   Zero-free region foundations: Eisenstein.FixedCuspArrays [0271_parallel1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.FixedCuspArrays
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/FixedCuspArrays.lean#L201-L388

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0011
import Definitions.Def_PNT_ZeroFree_433_0038
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0061
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0127_parallel1
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0168_parallel1
import Definitions.Def_PNT_ZeroFree_433_0195_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0241
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/FixedCuspArrays.lean
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein


open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O


def fixedCuspArrayIndex (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : Eis :=
  (u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3

def fixedCuspArrayEligible (I J:Ideal Eis) : Prop :=
  Squarefree I ∧ primaryGenerator I≠0 ∧ primaryGenerator J≠0

def fixedCuspArrayWeight (m:ℕ) (J:Ideal Eis) : ℝ :=
  (3:ℝ)^((m:ℝ)/6)*Real.sqrt (Ideal.absNorm J:ℝ)

lemma fixedCuspArrayWeight_nonneg (m:ℕ) (J:Ideal Eis) :
    0≤fixedCuspArrayWeight m J := by
  unfold fixedCuspArrayWeight
  positivity

lemma fixedCuspArrayWeight_pos (m:ℕ) (J:Ideal Eis) (hJ:primaryGenerator J≠0) :
    0<fixedCuspArrayWeight m J := by
  rw [fixedCuspArrayWeight,←primaryGenerator_norm J hJ]
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (norm_pos_iff.mpr (eisEmbedding_ne_zero hJ))


end CubicEisenstein

section
open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

namespace IdealGaussCRT
open CubicEisenstein

theorem finiteAdditiveFourierCoeff_crt {ι T : Type*} [Fintype ι]
    (R : ι→Type*) [CommRing T] [∀i,CommRing (R i)]
    [Fintype T] [∀i,Fintype (R i)] (e : T≃+*∀i,R i)
    (ψ : AddChar T ℂ) (φ : ∀i,R i→ℂ) (h : T) :
    finiteAdditiveFourierCoeff ψ (fun x=>∏i,φ i (e x i)) h=
      ∏i,finiteAdditiveFourierCoeff (coordinateAddChar R e ψ i) (φ i) (e h i) := by
  have hsum : (∑x:T,(∏i,φ i (e x i))*ψ (-h*x))=
      ∏i,∑x:R i,φ i x*coordinateAddChar R e ψ i (-(e h i)*x) := by
    calc
      _ = ∑x:T,∏i,φ i (e x i)*coordinateAddChar R e ψ i (-(e h i)*e x i) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [addChar_finite_crt_factor R e ψ (-h*x)]
        simp only [map_mul,map_neg,Pi.mul_apply,Pi.neg_apply,Finset.prod_mul_distrib]
      _ = ∑x:(∀i,R i),∏i,φ i (x i)*coordinateAddChar R e ψ i (-(e h i)*x i) :=
        Equiv.sum_comp e.toEquiv (fun x:∀i,R i=>∏i,φ i (x i)*coordinateAddChar R e ψ i (-(e h i)*x i))
      _ = _ := (Fintype.prod_sum (fun i (x:R i)=>φ i x*coordinateAddChar R e ψ i (-(e h i)*x))).symm
  have hcard : (Fintype.card T:ℂ)=∏i,(Fintype.card (R i):ℂ) := by
    rw [Fintype.card_congr e.toEquiv,Fintype.card_pi,Nat.cast_prod]
  simp only [finiteAdditiveFourierCoeff,hsum,hcard,Finset.prod_div_distrib]

theorem finite_fourier_weighted_crt {ι T : Type*} [Fintype ι]
    (R : ι→Type*) [CommRing T] [∀i,CommRing (R i)]
    [Fintype T] [∀i,Fintype (R i)] (e : T≃+*∀i,R i)
    (ψ : AddChar T ℂ) (φ κ : ∀i,R i→ℂ) :
    (∑h:T,finiteAdditiveFourierCoeff ψ (fun x=>∏i,φ i (e x i)) h *
      ∏i,κ i (e h i))=
      ∏i,∑h:R i,finiteAdditiveFourierCoeff (coordinateAddChar R e ψ i) (φ i) h*κ i h := by
  simp only [finiteAdditiveFourierCoeff_crt,←Finset.prod_mul_distrib]
  calc
    _ = ∑h:∀i,R i,∏i,finiteAdditiveFourierCoeff (coordinateAddChar R e ψ i) (φ i) (h i)*κ i (h i) :=
      Equiv.sum_comp e.toEquiv
        (fun h:∀i,R i=>∏i,finiteAdditiveFourierCoeff (coordinateAddChar R e ψ i) (φ i) (h i)*κ i (h i))
    _ = _ := (Fintype.prod_sum (fun i (h:R i)=>
      finiteAdditiveFourierCoeff (coordinateAddChar R e ψ i) (φ i) h*κ i h)).symm

end IdealGaussCRT

namespace LocalReflectionBrackets

section
open CubicEisenstein
variable {F : Type*} [Field F] [Fintype F]

def frequencyMultiplier (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x h : F) : ℂ :=
  if h=0 then 1 else (((χ⁻¹)^2) ((σ:F)*h))*ψ (((ε:F)*x)*h⁻¹)

def frequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (σ ε : Fˣ) (x h : F) : ℂ :=
  finiteAdditiveFourierCoeff ψ (fun t=>(χ^j) t) h*frequencyMultiplier χ ψ σ ε x h

lemma frequencyRow_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (σ ε : Fˣ) (x : F) :
    frequencyRow χ ψ j σ ε x 0=zeroFourierCoefficient χ j := by
  simp only [frequencyRow,frequencyMultiplier,finiteAdditiveFourierCoeff,
    zeroFourierCoefficient,ite_true,neg_zero,zero_mul,AddChar.map_zero_eq_one,
    mul_one,div_eq_mul_inv]
  ring

lemma frequencyRow_units (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (σ ε : Fˣ) (x : F) :
    (∑h:Fˣ,frequencyRow χ ψ j σ ε x h)=activeRow χ ψ j σ ε x := by
  unfold frequencyRow finiteAdditiveFourierCoeff frequencyMultiplier activeRow
  simp only [Units.ne_zero,ite_false,Units.val_inv_eq_inv_val,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  ring_nf

open ActualEisensteinCubic CompletedGauss
noncomputable local instance quotientFieldFrequency (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] :
    Field (ActualEisensteinCubic.O⧸P) := Ideal.Quotient.field P
noncomputable local instance quotientFintypeFrequency (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] :
    Fintype (ActualEisensteinCubic.O⧸P) := Fintype.ofFinite _

theorem canonical_frequencyRow_zero (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hgood : lambda∉P) (hchar : ringChar (ActualEisensteinCubic.O⧸P)≠2) (ψ : AddChar (ActualEisensteinCubic.O⧸P) ℂ)
    (j : ℕ) (hj : j<6) (σ ε : (ActualEisensteinCubic.O⧸P)ˣ) (x : ActualEisensteinCubic.O⧸P) :
    frequencyRow (actualSextic P hgood) ψ j σ ε x 0=
      if j=0 then 1-(Fintype.card (ActualEisensteinCubic.O⧸P):ℂ)⁻¹ else 0 := by
  rw [frequencyRow_zero]
  simpa only [actualSextic] using canonical_zeroFourierCoefficient P hgood hchar j hj

theorem canonical_frequencyRow_units (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hgood : lambda∉P) (hchar : ringChar (ActualEisensteinCubic.O⧸P)≠2) (ψ : AddChar (ActualEisensteinCubic.O⧸P) ℂ)
    (hψ : ψ.IsPrimitive) (j : ℕ) (hj : j<6) (σ ε : (ActualEisensteinCubic.O⧸P)ˣ) (x : ActualEisensteinCubic.O⧸P) :
    (∑h:(ActualEisensteinCubic.O⧸P)ˣ,frequencyRow (actualSextic P hgood) ψ j σ ε x h)=
      (((actualSextic P hgood)⁻¹)^2) σ *
        phase (actualSextic P hgood) ψ j ε*bracket (actualSextic P hgood) j x := by
  rw [frequencyRow_units]
  simpa only [actualSextic] using canonical_A5_normalized P hgood hchar ψ hψ j hj σ ε x

end

open ActualEisensteinCubic CubicEisenstein IdealGaussCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance quotientFintypeCrt (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _


end LocalReflectionBrackets
end


end

end OAI

end



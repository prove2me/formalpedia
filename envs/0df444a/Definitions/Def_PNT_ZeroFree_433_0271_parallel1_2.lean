-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0271_parallel1_2
-- name    : PNT_ZeroFree_433_0271_parallel1_2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:04:36.219785+00:00
-- url     : https://prove2.me/theorems/2689d569-1a68-4d1e-922a-11c2e31d054d
-- title:
--   Zero-free region foundations: Eisenstein.FixedCuspArrays [0271_parallel1_2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.FixedCuspArrays
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/FixedCuspArrays.lean#L390-L422

import Definitions.Def_PNT_ZeroFree_433_0271_parallel1_1

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


section
open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding


namespace LocalReflectionBrackets


open ActualEisensteinCubic CubicEisenstein IdealGaussCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O


theorem canonical_finite_reflection_crt {ι T : Type*} [Fintype ι]
    [CommRing T] [Fintype T]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (e : T≃+*∀i,Eis⧸P i) (ψ : AddChar T ℂ) (hψ : ψ.IsPrimitive)
    (hg : ∀i,lambda∉P i) (hchar : ∀i,ringChar (Eis⧸P i)≠2)
    (j : ι→ℕ) (hj : ∀i,j i<6) (σ ε : ∀i,(Eis⧸P i)ˣ) (x : ∀i,Eis⧸P i) :
    let χ := fun i=>actualSextic (P i) (hg i)
    let ψi := coordinateAddChar (fun i=>Eis⧸P i) e ψ
    (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) (e h i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈A,(((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i))*
        (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0) := by
  let (i : ι) : Field (Eis⧸P i) := Ideal.Quotient.field (P i)
  let χ := fun i=>actualSextic (P i) (hg i)
  let ψi := coordinateAddChar (fun i=>Eis⧸P i) e ψ
  let f := fun i=>frequencyRow (χ i) (ψi i) (j i) (σ i) (ε i) (x i)
  have hsum : (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) (e h i))=
      ∑h:∀i,Eis⧸P i,∏i,f i (h i) := by
    simp only [finiteAdditiveFourierCoeff_crt,←Finset.prod_mul_distrib]
    exact Equiv.sum_comp e.toEquiv (fun h:∀i,Eis⧸P i=>∏i,f i (h i))
  have hactive (i : ι) : (∑h:(Eis⧸P i)ˣ,f i h)=
      (((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i) := by
    exact canonical_frequencyRow_units (P i) (hg i) (hchar i) (ψi i)
      (coordinateAddChar_isPrimitive (fun i=>Eis⧸P i) e ψ hψ i) (j i) (hj i) (σ i) (ε i) (x i)
  have hzero (i : ι) : f i 0=if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0 := by
    exact canonical_frequencyRow_zero (P i) (hg i) (hchar i) (ψi i) (j i) (hj i) (σ i) (ε i) (x i)
  change (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) (e h i))=_
  rw [hsum,FixedRayActiveSet.product_sum_by_active_set (fun i=>Eis⧸P i) f]
  simp only [hactive,hzero]
  rfl


end LocalReflectionBrackets
end


end

end OAI

end



-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0271_parallel1
-- name    : PNT_ZeroFree_433_0271_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:06:40.534511+00:00
-- url     : https://prove2.me/theorems/9df859d8-5ad9-48ff-beef-1f357edc0904
-- title:
--   Zero-free region foundations: Eisenstein.FixedCuspArrays [0271_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.FixedCuspArrays
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/FixedCuspArrays.lean#L424-L500

import Definitions.Def_PNT_ZeroFree_433_0271_parallel1_2

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


theorem canonical_principal_reflection_crt {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀i,lambda∉P i) (hchar : ∀i,ringChar (Eis⧸P i)≠2)
    (j : ι→ℕ) (hj : ∀i,j i<6) (σ ε : ∀i,(Eis⧸P i)ˣ) (x : ∀i,Eis⧸P i)
    (c : Eis) (hc : c≠0) (hcP : Ideal.span {c}=∏i,P i)
    [Fintype (Eis⧸Ideal.span {c})] :
    let e := (Ideal.quotEquivOfEq hcP).trans (quotientProdEquivPi P hcop)
    let ψ := quotientTrace c hc
    let χ := fun i=>actualSextic (P i) (hg i)
    let ψi := coordinateAddChar (fun i=>Eis⧸P i) e ψ
    (∑h:Eis⧸Ideal.span {c},finiteAdditiveFourierCoeff ψ (principalSexticRow P hcop hg j c hcP) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) (e h i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈A,(((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i))*
        (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0) := by
  let e := (Ideal.quotEquivOfEq hcP).trans (quotientProdEquivPi P hcop)
  have hψ : (quotientTrace c hc).IsPrimitive :=
    GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc
  have hrow : principalSexticRow P hcop hg j c hcP=
      fun t=>∏i,(actualSextic (P i) (hg i)^j i) (e t i) := by
    funext t
    rfl
  dsimp only
  rw [hrow]
  exact canonical_finite_reflection_crt P e (quotientTrace c hc) hψ hg hchar j hj σ ε x

end LocalReflectionBrackets
end

namespace CubicEisenstein
open scoped Classical MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma upper_right_removed_bottom (M T:SL(2,Eis)) (hT:T 1 0=0) :
    (M*T⁻¹) 1 0=M 1 0*T 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,hT]

lemma upper_right_removed_top (M T:SL(2,Eis)) (hT:T 1 0=0) :
    (M*T⁻¹) 0 0=M 0 0*T 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,hT]

lemma upper_right_removed_last (M T:SL(2,Eis)) :
    (M*T⁻¹) 1 1= -M 1 0*T 0 1+M 1 1*T 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]

lemma upper_diagonal_product (T:SL(2,Eis)) (hT:T 1 0=0) : T 0 0*T 1 1=1 := by
  have hd:=T.property
  simpa only [Matrix.det_fin_two,hT,mul_zero,sub_zero] using hd

structure FixedCuspShape (H:SL(2,Eis)) where
  gamma : levelTwo
  index : Fin 3
  upper : SL(2,Eis)
  lower_zero : upper 1 0=0
  upper_unit : IsUnit (upper 0 0)
  lower_unit : IsUnit (upper 1 1)
  factorization : H=(gamma:SL(2,Eis))*cuspRepresentative index*upper

lemma exists_fixedCuspShape (H:SL(2,Eis)) : Nonempty (FixedCuspShape H) := by
  obtain ⟨G,j,T,hT,hT0,hT1,he⟩:=three_cusp_decomposition H
  exact ⟨⟨G,j,T,hT,hT0,hT1,he⟩⟩

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H) (g:levelTwo)

lemma removed_eq : (g:SL(2,Eis))*H*s.upper⁻¹=
    ((g*s.gamma:levelTwo):SL(2,Eis))*cuspRepresentative s.index := by
  calc
    _ = (g:SL(2,Eis))*((s.gamma:SL(2,Eis))*cuspRepresentative s.index*s.upper)*s.upper⁻¹ :=
      congrArg (fun K:SL(2,Eis)=>(g:SL(2,Eis))*K*s.upper⁻¹) s.factorization
    _ = _ := by simp only [Subgroup.coe_mul]; group


end FixedCuspShape
end CubicEisenstein


end

end OAI

end



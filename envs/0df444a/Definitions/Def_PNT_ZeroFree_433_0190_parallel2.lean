-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0190_parallel2
-- name    : PNT_ZeroFree_433_0190_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:31:54.382845+00:00
-- url     : https://prove2.me/theorems/fe0b9806-ae39-4dcb-9874-f1ff36b64d58
-- title:
--   Zero-free region foundations: Eisenstein.CoordinateLaplacian [0190_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CoordinateLaplacian
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CoordinateLaplacian.lean#L303-L615

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0049
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0087
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1
import Definitions.Def_PNT_ZeroFree_433_0128_parallel1
import Definitions.Def_PNT_ZeroFree_433_0130
import Definitions.Def_PNT_ZeroFree_433_0131
import Definitions.Def_PNT_ZeroFree_433_0132
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0146_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148_parallel1
import Definitions.Def_PNT_ZeroFree_433_0151_parallel1
import Definitions.Def_PNT_ZeroFree_433_0159_parallel1
import Definitions.Def_PNT_ZeroFree_433_0178_parallel1
import Definitions.Def_PNT_ZeroFree_433_0189_parallel1
import Definitions.Def_PNT_ZeroFree_433_0190_parallel1
import Definitions.Def_PNT_ZeroFree_433_0194_parallel1
import Definitions.Def_PNT_ZeroFree_433_0196_parallel1
import Definitions.Def_PNT_ZeroFree_433_0199_parallel1
import Definitions.Def_PNT_ZeroFree_433_0215_parallel2
import Definitions.Def_PNT_ZeroFree_433_0227_parallel2
import Definitions.Def_PNT_ZeroFree_433_0230_parallel1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0236_parallel1
import Definitions.Def_PNT_ZeroFree_433_0243_parallel2
import Definitions.Def_PNT_ZeroFree_433_0248_parallel1
import Definitions.Def_PNT_ZeroFree_433_0253_parallel1
import Definitions.Def_PNT_ZeroFree_433_0263_parallel2
import Definitions.Def_PNT_ZeroFree_433_0266_parallel1
import Definitions.Def_PNT_ZeroFree_433_0270_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CoordinateLaplacian.lean
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
open MeasureTheory


namespace SecondPassArithmetic
open ActualEisensteinCubic FirstPassCubeLabels ConcreteTraceCRT

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

def globalCanonicalLabels (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex) : Finset (Ideal ActualEisensteinCubic.O) :=
  (globalArithmeticTargets p source side q j).image Prod.fst

include hp in
theorem globalCanonicalLabels_bounds (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hk : ∀x∈source,x.source.frequency≠0) :
    ∀I∈globalCanonicalLabels p source side q j,
      I≠⊥ ∧ Squarefree I ∧ (Ideal.absNorm I:ℝ)≤globalPooledLabelScale j := by
  intro I hI
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hI
  have hb := globalArithmeticTargets_bounds p hp source side q j hk z hz
  exact ⟨hb.1,globalArithmeticTargets_squarefree p source side q j z hz,hb.2.1⟩

end SecondPassArithmetic
end

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct jLabel)

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O)

omit [DecidableEq ι] in
theorem actualSecondLabel_coprime (bad : Ideal ActualEisensteinCubic.O)
    (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (B C E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    IsCoprime (actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂) bad := by
  have hprod (S : Finset ι) : IsCoprime (∏i∈S,Ideal.span {p i}) bad :=
    IsCoprime.prod_left (fun i _=>hbad i)
  have hJ : IsCoprime (Ideal.span {jLabel p B (fun i=>v₁ i+v₂ i) ε₁ ε₂}) bad := by
    simp only [jLabel,primeProduct,FiniteGaussPhase.span_finset_prod,←Ideal.span_singleton_pow]
    exact IsCoprime.prod_left (fun i _=>(hbad i).pow_left)
  exact ((hJ.mul_left (hprod C)).mul_left (hprod E)).mul_left (hprod V)

theorem globalNewLabel_coprime (bad : Ideal ActualEisensteinCubic.O)
    (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad) (x : GlobalSecondData ι) :
    IsCoprime (SecondPassFiber.newLabel (globalSecondTuple p x)) bad := by
  exact actualSecondLabel_coprime p bad hbad x.cube.support x.common x.source.divisor x.source.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit

theorem globalCanonicalLabels_coprime (bad : Ideal ActualEisensteinCubic.O)
    (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex) :
    ∀I∈globalCanonicalLabels p source side q j,IsCoprime I bad := by
  intro I hI
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  exact globalNewLabel_coprime p bad hbad x

end SecondPassArithmetic


open scoped BigOperators Classical
namespace CanonicalCoefficientClass

section
open ActualEisensteinCubic
open SecondPassArithmetic (rayMonoid conjugateRayMonoid rayMonoid_apply conjugateRayMonoid_apply
  FirstCoreIndex firstCoreTwist sideRayMonoid SecondRayIndex secondRayMinus secondRayPlus)
open RayFourExpansion (RayCharacter)


def initialBase {q : ℕ} (χ : DirichletCharacter ℂ q) : ActualEisensteinCubic.O→*ℂ :=
  InitialMeanSquare.conjugateMonoid (InitialMeanSquare.normCharacter χ)

lemma initialBase_norm {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ActualEisensteinCubic.O) :
    ‖initialBase χ x‖≤1 := by
  change ‖star (InitialMeanSquare.normCharacter χ x)‖≤1
  rw [norm_star]
  exact InitialMeanSquare.normCharacter_norm_le_one χ x

lemma initial_minus_member {q : ℕ} (χ : DirichletCharacter ℂ q) (r : SecondRayIndex) :
    IsBaseRayTwist (initialBase χ) (secondRayMinus (initialBase χ) r) :=
  IsBaseRayTwist.secondMinus (Or.inl rfl : IsBaseRayTwist (initialBase χ) (initialBase χ)) r

lemma initial_plus_member {q : ℕ} (χ : DirichletCharacter ℂ q) (r : SecondRayIndex) :
    IsBaseRayTwist (initialBase χ) (secondRayPlus (initialBase χ) r) :=
  IsBaseRayTwist.secondPlus (Or.inl rfl : IsBaseRayTwist (initialBase χ) (initialBase χ)) r

end

open ActualEisensteinCubic
open ActualEisensteinCoordinates (eval coords eval_coords)
open ShortDraftLatticeCount (qNat qO_nonneg coords_eval)


theorem normCharacter_factorsModulo {m : ℕ} (χ : DirichletCharacter ℂ m) :
    FactorsModulo (Ideal.span {(m : ActualEisensteinCubic.O)}) (InitialMeanSquare.normCharacter χ) := by
  intro x y hxy
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hxy
  let c := (coords y).1
  let d := (coords y).2
  let e := (coords z).1
  let f := (coords z).2
  have hy : y=eval c d := (eval_coords y).symm
  have hx : x=eval (c+(m : ℤ)*e) (d+(m : ℤ)*f) := by
    calc
      x=y+(m : ActualEisensteinCubic.O)*z := by linear_combination hz
      _=eval (c+(m : ℤ)*e) (d+(m : ℤ)*f) := by
        rw [hy,←eval_coords z]
        dsimp [eval,c,d,e,f]
        push_cast
        ring
  change χ (Ideal.absNorm (Ideal.span {x}))=χ (Ideal.absNorm (Ideal.span {y}))
  congr 1
  rw [hx,hy,norm_eval_mod,norm_eval_mod]
  simp

theorem initialBase_factorsModulo {m : ℕ} (χ : DirichletCharacter ℂ m) :
    FactorsModulo (Ideal.span {(m : ActualEisensteinCubic.O)}) (initialBase χ) := by
  intro x y hxy
  change star (InitialMeanSquare.normCharacter χ x)=star (InitialMeanSquare.normCharacter χ y)
  rw [normCharacter_factorsModulo χ x y hxy]


theorem initialOrbit_factorsModulo {m : ℕ} (χ : DirichletCharacter ℂ m) (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : IsBaseRayTwist (initialBase χ) Ψ) : FactorsModulo (fixedBaseConductor m) Ψ :=
  hΨ.factorsModulo _ (initialBase_factorsModulo χ)


end CanonicalCoefficientClass

end

end OAI

end



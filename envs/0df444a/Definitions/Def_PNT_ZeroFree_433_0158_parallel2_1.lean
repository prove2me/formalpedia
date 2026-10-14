-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0158_parallel2_1
-- name    : PNT_ZeroFree_433_0158_parallel2_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:41:45.960303+00:00
-- url     : https://prove2.me/theorems/42e3e106-442c-41ac-ac7d-8afa6e0b0925
-- title:
--   Zero-free region foundations: MeanSquare.PoissonSource [0158_parallel2_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.MeanSquare.PoissonSource
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/PoissonSource.lean#L146-L605

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0059
import Definitions.Def_PNT_ZeroFree_433_0060
import Definitions.Def_PNT_ZeroFree_433_0061
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0066
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0079
import Definitions.Def_PNT_ZeroFree_433_0079_1
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0087
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0107
import Definitions.Def_PNT_ZeroFree_433_0116
import Definitions.Def_PNT_ZeroFree_433_0117
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1
import Definitions.Def_PNT_ZeroFree_433_0123_parallel2
import Definitions.Def_PNT_ZeroFree_433_0125_parallel1
import Definitions.Def_PNT_ZeroFree_433_0126_parallel2
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148_parallel2
import Definitions.Def_PNT_ZeroFree_433_0158_parallel1
import Definitions.Def_PNT_ZeroFree_433_0245_parallel1
import Definitions.Def_PNT_ZeroFree_433_0265_parallel1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/PoissonSource.lean
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
namespace InitialMeanSquare


open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma initial_actual_row_norm (x : SecondExpansionData ι) :
    ‖eisEmbedding (actualSecondRow p ∅ x.divisor x.frequency)‖^2 =
      elementNorm (sourceObservation p x).1 := by
  simp only [actualSecondRow, sourceObservation, elementNorm,
    map_mul, norm_mul, mul_pow, primeSubsetGenerator_norm_eq_productNorm,
    primeProductNorm, Finset.prod_empty, map_one, norm_one, one_pow, one_mul]


end


end InitialMeanSquare

open scoped BigOperators


open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient)
open FirstPassCubeLabels

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})


theorem canonicalSourceCoefficient_union
    (hpr : ∀ i,lambda^2∣p i-1) (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (D S : Finset ι) (hd : Disjoint D S) :
    canonicalSourceCoefficient p hp hcop hg Ψ m f H (D∪S) =
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) D *
      (columnCoefficient p hp hcop hg S *
        multiplicativeCoreColumn p Ψ m (fun U => H (D∪U)) S *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (∏i∈D,p i)^4 *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S f^4) := by
  have hA := columnCoefficient_union_row_four p hp hcop hg hpr S D hd.symm
  rw [Finset.union_comm S D] at hA
  simp only [canonicalSourceCoefficient,hA,Finset.prod_union hd,map_mul,
    row_union _ hg D S hd,mask_union _ hg D S hd,mul_pow,multiplicativeCoreColumn]
  ring


theorem canonicalSourceCoefficient_cube_split
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,lambda^2∣p i-1) (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (B C S : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (hCB : Disjoint C B) (hSC : Disjoint S C) (hSB : Disjoint S B) :
    let A := B.filter (fun i => if negative then ε₂ i else ε₁ i)
    canonicalSourceCoefficient p hp hcop hg Ψ m f H ((A∪C)∪S) =
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) (A∪C) *
      (columnCoefficient p hp hcop hg S *
        originalLabelColumn p hg B ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m (fun U => H ((A∪C)∪U)))
          (∏i∈C,p i) f S) := by
  dsimp only
  have hAC : Disjoint (B.filter fun i => if negative then ε₂ i else ε₁ i) C :=
    hCB.symm.mono_left (Finset.filter_subset _ _)
  have hAS : Disjoint (B.filter fun i => if negative then ε₂ i else ε₁ i) S :=
    hSB.symm.mono_left (Finset.filter_subset _ _)
  rw [canonicalSourceCoefficient_union p hp hcop hg hpr Ψ m f H _ S
    (Finset.disjoint_union_left.mpr ⟨hAS,hSC.symm⟩)]
  have hA : (∏i∈B.filter (fun i => if negative then ε₂ i else ε₁ i),p i) =
      aLabel p B (if negative then ε₂ else ε₁) := by
    cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,aLabel,primeProduct,
      Finset.prod_filter,bit]
    all_goals
      apply Finset.prod_congr rfl
      intro i hi
      split_ifs <;> simp_all
  rw [Finset.prod_union hAC,hA]
  simp only [originalLabelColumn,cubeRadical,commonProduct_mask p hg hinj S B,if_pos hSB,mul_one]
  ring

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnCoefficient columnPrimeCoprime)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})


theorem canonicalPair_first_poisson
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (M N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) :
    (V₁ (columnLog p X₁ N)*V₂ (columnLog p X₂ P))*
      (star (columnCoefficient p hp hcop hg N*C₁ N)*(columnCoefficient p hp hcop hg P*C₂ P))*
      (∑'z:O,rowCoprimeMask (fun i=>Ideal.span {p i}) M z*
        blockRow p hg ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)
          (threeBlockExponent N P v ε₁ ε₂) z*W (‖eisEmbedding z‖^2/K)) =
    ∑D∈M.powerset,(UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/
      (primeProductNorm p D:ℂ)*
      ∑'h:O,canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h := by
  have he : ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i≠0 := by
    intro i hi
    by_cases hn:i∈N
    · simp [threeBlockExponent,hn]
    by_cases hp':i∈P
    · simp [threeBlockExponent,hn,hp']
    · have hiC:i∈cubeActiveSupport B v ε₁ ε₂ := by simpa [hn,hp'] using hi
      simp only [threeBlockExponent,if_neg hn,if_neg hp']
      exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2
  have he6 : ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i<6 := by
    intro i hi
    unfold threeBlockExponent
    split_ifs <;> first | omega | exact ZMod.val_lt _
  rw [masked_block_radial_poisson_product p hp hinj hcop hg hc M _ _ he he6 W K hK]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  simp only [←tsum_mul_left]
  apply tsum_congr
  intro h
  dsimp only [canonicalPairMode,threeGaussRowFactor]
  rw [SecondPassArithmetic.primeSubsetGenerator_norm_eq_productNorm p D]
  simp only [primeProductNorm]
  ring


theorem disjointCanonicalSource_poisson
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (F M B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) :
    disjointCanonicalSource p hp hcop hg F M B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K =
    ∑D∈M.powerset,(UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/
      (primeProductNorm p D:ℂ)*
      ∑'h:O,actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h := by
  simp_rw [tsum_actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK _
    (primeSubsetGenerator_ne_zero _ _)]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP : Disjoint N P
  · simp only [hNP,ite_true]
    exact canonicalPair_first_poisson p hp hcop hg hinj hc M N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK
  · simp only [hNP,ite_false,mul_zero,Finset.sum_const_zero]

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
open MixedCrossSeparation (columnCoefficient)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})


def canonicalCubeOuter (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) : ℂ :=
  star (canonicalSourceCoefficient p hp hcop hg Ψ₁ m₁ f (fun _=>1) (b.rightDivisor∪C))*
    canonicalSourceCoefficient p hp hcop hg Ψ₂ m₂ f (fun _=>1) (b.leftDivisor∪C)

def canonicalCubeResidual (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) : Finset ι→ℂ :=
  originalLabelColumn p hg b.support b.leftBit b.rightBit negative
    (multiplicativeCoreColumn p Ψ m (fun S=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪S)))
    (∏i∈C,p i) f


end SecondPassArithmetic

end

end OAI

end



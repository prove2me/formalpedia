-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0255_parallel2
-- name    : PNT_ZeroFree_433_0255_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:48:06.597747+00:00
-- url     : https://prove2.me/theorems/b3689e1d-e447-4dc3-8214-7255ee80684c
-- title:
--   Zero-free region foundations: Eisenstein.CubeEigenrelation [0255_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CubeEigenrelation
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CubeEigenrelation.lean#L345-L598

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0123_parallel1
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0136
import Definitions.Def_PNT_ZeroFree_433_0232_parallel2
import Definitions.Def_PNT_ZeroFree_433_0238_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel2
import Definitions.Def_PNT_ZeroFree_433_0243_parallel3
import Definitions.Def_PNT_ZeroFree_433_0245
import Definitions.Def_PNT_ZeroFree_433_0246_parallel1
import Definitions.Def_PNT_ZeroFree_433_0246_parallel2
import Definitions.Def_PNT_ZeroFree_433_0247_parallel1
import Definitions.Def_PNT_ZeroFree_433_0249_parallel1
import Definitions.Def_PNT_ZeroFree_433_0255_parallel1
import Definitions.Def_PNT_ZeroFree_433_0267_parallel1
import Definitions.Def_PNT_ZeroFree_433_0285_parallel1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CubeEigenrelation.lean
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


open scoped Classical


namespace CubicKubota
open scoped BigOperators Classical MatrixGroups

open CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma literalCube_zero_pair (p : ActualEisensteinCubic.O) (hp : p≠0) (x : cubeKernelCorrespondence p) :
    cubeAverageMatrix p hp 0*integralComplexMatrix (cubeKernelRightGlobal p hp x)=
      integralComplexMatrix (cubeKernelLeftGlobal p x)*cubeAverageMatrix p hp 0 := by
  let M := cubeKernelLeftGlobal p x
  let N := cubeKernelRightGlobal p hp x
  let z := cubeDilationRoot p
  have hz : z^2=eisEmbedding p^3 := cubeDilationRoot_sq p
  have hz0 : z≠0 := cubeDilationRoot_ne_zero p hp
  have he := cubeCorrespondence_entries p x.1
  change p^3*M 0 0=N 0 0*p^3 ∧ p^3*M 0 1=N 0 1 ∧
    M 1 0=N 1 0*p^3 ∧ M 1 1=N 1 1 at he
  have h00 : eisEmbedding (M 0 0)=eisEmbedding (N 0 0) :=
    congrArg eisEmbedding (mul_left_cancel₀ (pow_ne_zero 3 hp) (he.1.trans (mul_comm _ _)))
  have h01 := congrArg eisEmbedding he.2.1
  have h10 := congrArg eisEmbedding he.2.2.1
  have h11 := congrArg eisEmbedding he.2.2.2
  simp only [map_mul,map_pow] at h01 h10
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
      cubeAverageMatrix_entries,integralComplexMatrix_apply]
  · change z⁻¹*eisEmbedding (N 0 0)+(z⁻¹*(3*eisEmbedding 0))*eisEmbedding (N 1 0)=
      eisEmbedding (M 0 0)*z⁻¹+eisEmbedding (M 0 1)*0
    rw [h00,map_zero]
    ring
  · change z⁻¹*eisEmbedding (N 0 1)+(z⁻¹*(3*eisEmbedding 0))*eisEmbedding (N 1 1)=
      eisEmbedding (M 0 0)*(z⁻¹*(3*eisEmbedding 0))+eisEmbedding (M 0 1)*z
    rw [←h01,←hz,map_zero]
    field_simp [hz0]
    ; ring
  · change 0*eisEmbedding (N 0 0)+z*eisEmbedding (N 1 0)=
      eisEmbedding (M 1 0)*z⁻¹+eisEmbedding (M 1 1)*0
    rw [h10,←hz]
    field_simp [hz0]
    ; ring
  · change 0*eisEmbedding (N 0 1)+z*eisEmbedding (N 1 1)=
      eisEmbedding (M 1 0)*(z⁻¹*(3*eisEmbedding 0))+eisEmbedding (M 1 1)*z
    rw [h11,map_zero]
    ring

theorem literalCube_zero_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) :
    IntegralCoverIntertwines (cubeKernelRangeEquiv p hp).symm (cubeAverageMatrix p hp 0) := by
  intro r
  let x := (MonoidHom.ofInjective (cubeKernelRightGlobal_injective p hp)).symm r
  have hr : cubeKernelRightGlobal p hp x=(r:SL(2,ActualEisensteinCubic.O)) :=
    MonoidHom.apply_ofInjective_symm (cubeKernelRightGlobal_injective p hp) r
  change cubeAverageMatrix p hp 0*integralComplexMatrix (r:SL(2,ActualEisensteinCubic.O))=
    integralComplexMatrix (cubeKernelLeftGlobal p x)*cubeAverageMatrix p hp 0
  rw [←hr]
  exact literalCube_zero_pair p hp x


lemma cubeAverageMatrix_factor_zero (p : ActualEisensteinCubic.O) (hp : p≠0) (q : ActualEisensteinCubic.O) :
    cubeAverageMatrix p hp q=cubeAverageMatrix p hp 0*
      integralComplexMatrix (upperTranslation q:SL(2,ActualEisensteinCubic.O)) := by
  rw [cubeTranslation_complex]
  have h0 : complexTranslation 0=1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [complexTranslation]
  simp only [cubeAverageMatrix,map_zero,mul_zero,h0,mul_one]

theorem literalCube_summand_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) (q : ActualEisensteinCubic.O)
    (A : SL(2,ActualEisensteinCubic.O)) (r : (cubeKernelRightGlobal p hp).range)
    (hA : (upperTranslation q:SL(2,ActualEisensteinCubic.O))*A=(r:SL(2,ActualEisensteinCubic.O))*(upperTranslation q:SL(2,ActualEisensteinCubic.O))) :
    cubeAverageMatrix p hp q*integralComplexMatrix A=
      integralComplexMatrix ((cubeKernelRangeEquiv p hp).symm r:SL(2,ActualEisensteinCubic.O))*cubeAverageMatrix p hp q := by
  have hAc := congrArg integralComplexMatrix hA
  simp only [map_mul] at hAc
  rw [cubeAverageMatrix_factor_zero,mul_assoc,hAc,←mul_assoc,
    literalCube_zero_intertwines p hp r,mul_assoc]

end CubicKubota

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma integralCoverIntertwines_trans {H J K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (f : J≃*K) (g h : SL(2,ℂ))
    (he : IntegralCoverIntertwines e g) (hf : IntegralCoverIntertwines f h) :
    IntegralCoverIntertwines (e.trans f) (h*g) := by
  intro x
  change (h*g)*integralComplexMatrix (x:SL(2,ActualEisensteinCubic.O))=
    integralComplexMatrix (f (e x):SL(2,ActualEisensteinCubic.O))*(h*g)
  rw [mul_assoc,he x,←mul_assoc,hf (e x),mul_assoc]

lemma integralConjugateMap_trans {H J K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (f : J≃*K) (g h : SL(2,ℂ))
    (he : IntegralCoverIntertwines e g) (hf : IntegralCoverIntertwines f h)
    (q : IntegralOrbitQuotient H) :
    integralConjugateMap f h hf (integralConjugateMap e g he q)=
      integralConjugateMap (e.trans f) (h*g) (integralCoverIntertwines_trans e f g h he hf) q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection K (h•(g•w))=integralOrbitProjection K ((h*g)•w)
    rw [mul_smul]


end CubicEisenstein

open scoped Classical MatrixGroups BigOperators

namespace CubicKubota
open CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O


def cubeCommonTarget (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) : Subgroup (SL(2,ActualEisensteinCubic.O)) :=
  FiniteAutomorphismCover.target globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeKernelLeftGlobal p).range
    (cubeCommonAutomorphism p) (cubeKernelRangeEquiv p hp).symm r

lemma cubeCommonTarget_le (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    cubeCommonTarget p hp r≤globalKubotaKernel :=
  FiniteAutomorphismCover.target_le_common_ambient _ _ _ _ _ (cubeKernelLeftGlobal_le p) r


def cubeCommonEquiv (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    cubeCommonCover p hp≃*cubeCommonTarget p hp r :=
  FiniteAutomorphismCover.equiv globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeKernelLeftGlobal p).range
    (cubeCommonAutomorphism p) (cubeKernelRangeEquiv p hp).symm r

lemma cubeCommon_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    IntegralCoverIntertwines (cubeCommonEquiv p hp r)
      (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r)) := by
  intro h
  let q := GaussianShiftedPartition.representative (p^3) r
  let rh := FiniteAutomorphismCover.toSource globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeCommonAutomorphism p) r h
  have hA : (upperTranslation q:SL(2,ActualEisensteinCubic.O))*(h:SL(2,ActualEisensteinCubic.O))=
      (rh:SL(2,ActualEisensteinCubic.O))*(upperTranslation q:SL(2,ActualEisensteinCubic.O)) := by
    change (upperTranslation q:SL(2,ActualEisensteinCubic.O))*(h:SL(2,ActualEisensteinCubic.O))=
      ((upperTranslation q:SL(2,ActualEisensteinCubic.O))*(h:SL(2,ActualEisensteinCubic.O))*(upperTranslation q:SL(2,ActualEisensteinCubic.O))⁻¹)*
        (upperTranslation q:SL(2,ActualEisensteinCubic.O))
    simp only [mul_assoc,inv_mul_cancel,mul_one]
  exact literalCube_summand_intertwines p hp q (h:SL(2,ActualEisensteinCubic.O)) rh hA


end CubicKubota

end

end OAI

end



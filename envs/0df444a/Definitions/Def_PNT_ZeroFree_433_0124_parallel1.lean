-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0124_parallel1
-- name    : PNT_ZeroFree_433_0124_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:40:24.672391+00:00
-- url     : https://prove2.me/theorems/6be4da0f-9287-47cd-85ae-c4a6daaac254
-- title:
--   Zero-free region foundations: Eisenstein.QuotientTopology [0124_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.QuotientTopology
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/QuotientTopology.lean#L81-L713

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0059
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0100
import Definitions.Def_PNT_ZeroFree_433_0102
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0107
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1
import Definitions.Def_PNT_ZeroFree_433_0123_parallel1
import Definitions.Def_PNT_ZeroFree_433_0123_parallel2
import Definitions.Def_PNT_ZeroFree_433_0127_parallel1
import Definitions.Def_PNT_ZeroFree_433_0168_parallel1
import Definitions.Def_PNT_ZeroFree_433_0195_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/QuotientTopology.lean
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

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota
local notation "O" => ActualEisensteinCubic.O

instance complexSLTopology : TopologicalSpace (SL(2,ℂ)) :=
  inferInstanceAs (TopologicalSpace {A : Matrix (Fin 2) (Fin 2) ℂ // A.det=1})

lemma continuous_complexSL_coe :
    Continuous (fun g : SL(2,ℂ) => (g : Matrix (Fin 2) (Fin 2) ℂ)) :=
  continuous_subtype_val

lemma continuous_complexSL_mul (g : SL(2,ℂ)) :
    Continuous (fun h : SL(2,ℂ) => g*h) := by
  apply Continuous.subtype_mk
  change Continuous (fun h : SL(2,ℂ) =>
    (g : Matrix (Fin 2) (Fin 2) ℂ)*(h : Matrix (Fin 2) (Fin 2) ℂ))
  exact continuous_const.mul continuous_complexSL_coe

lemma continuous_coordinateSection : Continuous coordinateSection := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hroot : Continuous (fun w : UpperCoordinates => (Real.sqrt w.1.2 : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (continuous_snd.comp continuous_subtype_val))
  have hne : ∀w : UpperCoordinates,(Real.sqrt w.1.2 : ℂ)≠0 := fun w =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr w.2).ne'
  fin_cases i <;> fin_cases j
  · exact hroot
  · exact (continuous_fst.comp continuous_subtype_val).div hroot hne
  · exact continuous_const
  · exact hroot.inv₀ hne

lemma continuous_hyperbolicProjection :
    Continuous (fun g : SL(2,ℂ) => (g : HyperbolicSpace)) :=
  continuous_quotient_mk'

lemma continuous_upperCoordinates :
    Continuous (fun w : UpperCoordinates => upperPoint w.1.1 w.1.2 w.2) :=
  continuous_hyperbolicProjection.comp continuous_coordinateSection

lemma continuous_translatedUpperCoordinates (g : SL(2,ℂ)) :
    Continuous (fun w : UpperCoordinates => g • upperPoint w.1.1 w.1.2 w.2) := by
  exact continuous_hyperbolicProjection.comp
    ((continuous_complexSL_mul g).comp continuous_coordinateSection)

def integralOrbitRel (H : Subgroup (SL(2,O))) : Setoid HyperbolicSpace where
  r w w' := ∃h : H, integralComplexMatrix (h:SL(2,O)) • w = w'
  iseqv := ⟨by intro w; exact ⟨1,by simp⟩,
    by
      rintro w w' ⟨h,hh⟩
      refine ⟨h⁻¹,?_⟩
      rw [←hh]
      simp [←mul_smul],
    by
      rintro w w' w'' ⟨h,hh⟩ ⟨k,hk⟩
      refine ⟨k*h,?_⟩
      simpa only [Subgroup.coe_mul,map_mul,mul_smul,hh] using hk⟩

abbrev IntegralOrbitQuotient (H : Subgroup (SL(2,O))) := Quotient (integralOrbitRel H)

def integralOrbitProjection (H : Subgroup (SL(2,O))) :
    HyperbolicSpace → IntegralOrbitQuotient H := Quotient.mk _

lemma continuous_integralOrbitProjection (H : Subgroup (SL(2,O))) :
    Continuous (integralOrbitProjection H) := continuous_quotient_mk'

lemma integralOrbitProjection_eq (H : Subgroup (SL(2,O))) (h : H) (w : HyperbolicSpace) :
    integralOrbitProjection H (integralComplexMatrix (h:SL(2,O)) • w)=
      integralOrbitProjection H w := by
  apply Eq.symm
  exact Quotient.sound ⟨h,rfl⟩

end

open CubicKubota
local notation "O" => ActualEisensteinCubic.O

def truncatedFordLift (T : ℝ) (p : truncatedFordBox T) : UpperCoordinates :=
  ⟨p.1,lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2/3)) p.2.2.1⟩

lemma continuous_truncatedFordLift (T : ℝ) : Continuous (truncatedFordLift T) :=
  continuous_subtype_val.subtype_mk _

def fordOrbitChart (H : Subgroup (SL(2,O))) (r : SL(2,O)) (p : UpperCoordinates) :
    IntegralOrbitQuotient H := integralOrbitProjection H
      (integralComplexMatrix r⁻¹ • upperPoint p.1.1 p.1.2 p.2)

lemma continuous_fordOrbitChart (H : Subgroup (SL(2,O))) (r : SL(2,O)) :
    Continuous (fordOrbitChart H r) :=
  (continuous_integralOrbitProjection H).comp
    (continuous_translatedUpperCoordinates (integralComplexMatrix r⁻¹))

def compactFordCore (H : Subgroup (SL(2,O))) (S : Finset (SL(2,O))) (T : ℝ) :
    Set (IntegralOrbitQuotient H) :=
  ⋃r∈S, Set.range (fun p : truncatedFordBox T => fordOrbitChart H r (truncatedFordLift T p))

lemma compactFordCore_isCompact (H : Subgroup (SL(2,O))) (S : Finset (SL(2,O))) (T : ℝ) :
    IsCompact (compactFordCore H S T) := by
  let : CompactSpace (truncatedFordBox T) :=
    isCompact_iff_compactSpace.mp (truncatedFordBox_isCompact T)
  apply S.isCompact_biUnion
  intro r hr
  exact isCompact_range ((continuous_fordOrbitChart H r).comp (continuous_truncatedFordLift T))

def fordCuspTail (H : Subgroup (SL(2,O))) (r : SL(2,O)) (T : ℝ) :
    Set (IntegralOrbitQuotient H) :=
  fordOrbitChart H r '' {p : UpperCoordinates | Complex.normSq p.1.1≤1/3 ∧
    Real.sqrt (2/3)≤p.1.2 ∧ T<p.1.2}

theorem finiteIndex_compact_core_cusp_cover (H : Subgroup (SL(2,O))) [H.FiniteIndex] :
    ∃S : Finset (SL(2,O)), ∀T : ℝ,
      IsCompact (compactFordCore H S T) ∧
      Set.univ=compactFordCore H S T ∪ ⋃r∈S, fordCuspTail H r T := by
  obtain ⟨S,hS⟩ := finiteIndex_ford_cover H
  refine ⟨S,fun T => ⟨compactFordCore_isCompact H S T,?_⟩⟩
  apply Set.Subset.antisymm
  · intro q hq
    induction q using Quotient.inductionOn with | _ w =>
      obtain ⟨h,r,hr,z,v,hv,heq,hz,hfloor⟩ := hS w
      have hqeq : integralOrbitProjection H w=fordOrbitChart H r ⟨(z,v),hv⟩ := by
        rw [←integralOrbitProjection_eq H h w,heq]
        rfl
      change integralOrbitProjection H w∈_
      rw [hqeq]
      by_cases hT : v≤T
      · apply Or.inl
        apply Set.mem_iUnion.mpr
        refine ⟨r,Set.mem_iUnion.mpr ⟨hr,?_⟩⟩
        exact ⟨⟨(z,v),mem_truncatedFordBox z v T hz hfloor hT⟩,rfl⟩
      · apply Or.inr
        apply Set.mem_iUnion.mpr
        refine ⟨r,Set.mem_iUnion.mpr ⟨hr,?_⟩⟩
        exact ⟨⟨(z,v),hv⟩,⟨hz,hfloor,lt_of_not_ge hT⟩,rfl⟩
  · exact Set.subset_univ _

theorem levelThree_compact_core_cusp_cover :
    ∃S : Finset (SL(2,O)), ∀T : ℝ,
      IsCompact (compactFordCore levelThree S T) ∧
      Set.univ=compactFordCore levelThree S T ∪ ⋃r∈S, fordCuspTail levelThree r T := by
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  exact finiteIndex_compact_core_cusp_cover levelThree

theorem globalKubotaKernel_compact_core_cusp_cover :
    ∃S : Finset (SL(2,O)), ∀T : ℝ,
      IsCompact (compactFordCore globalKubotaKernel S T) ∧
      Set.univ=compactFordCore globalKubotaKernel S T ∪ ⋃r∈S, fordCuspTail globalKubotaKernel r T := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact finiteIndex_compact_core_cusp_cover globalKubotaKernel

end CubicEisenstein

namespace SecondPassArithmetic

section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory

section
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (tupleSourceSum densityChildEnergy)
open JointLogSeparation (outerWindow)

local instance p2mAnonymous_PNT_ZeroFree_433_0124_parallel1_1 {ι : Type*} : Nonempty (GlobalSecondData ι) :=
  ⟨⟨⟨0,0,∅,∅⟩,∅,∅,∅,⟨∅,∅,∅,0⟩⟩⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondRecover (s : Finset (GlobalSecondData ι)) : SecondPassFiber.OldTuple → GlobalSecondData ι :=
  Function.invFunOn (globalSecondTuple p) s

theorem globalSecondRecover_apply
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (s : Finset (GlobalSecondData ι)) (q : Ideal O × Ideal O × Ideal O)
    (hs : ∀ x∈s,GlobalSecondAdmissible x) (hq : ∀ x∈s,globalSecondFixedTriple p x=q)
    (x : GlobalSecondData ι) (hx : x∈s) :
    globalSecondRecover p s (globalSecondTuple p x)=x := by
  have hi : Set.InjOn (globalSecondTuple p) s := by
    intro x hx y hy h
    exact globalSecondEncoding_injective p hinj (hs x hx) (hs y hy) ((hq x hx).trans (hq y hy).symm) h
  exact hi.leftInvOn_invFunOn hx


end

open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label)
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (densityChildEnergy)
open JointLogSeparation (outerWindow)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondRawPool (F : Finset ι) (x : GlobalSecondData ι) : Finset ι :=
  (F\(x.cube.support∪x.common))\x.firstCommon

def globalSecondRawMask (m : O) (x : GlobalSecondData ι) : O :=
  m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
    x.cube.leftBit x.cube.rightBit *
    primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)


end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct jLabel b0Label cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

namespace CubeCoordinates
def sideDivisor {ι : Type*} (x : CubeCoordinates ι) (side : Bool) : Finset ι :=
  if side then x.leftDivisor else x.rightDivisor
end CubeCoordinates

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalCubeJNorm (x : GlobalSecondData ι) : ℝ :=
  ‖eisEmbedding (jLabel p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
    x.cube.leftBit x.cube.rightBit)‖^2

def globalCubeActiveRoot (x : GlobalSecondData ι) : ℝ :=
  ‖eisEmbedding (∏ i∈cubeActiveSupport x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖

def globalFirstColumnScale (ell : ℝ) (x : GlobalSecondData ι) (side : Bool) : ℝ :=
  ell/(primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common)

def globalFirstRowScale (K ell B F : ℝ) (x : GlobalSecondData ι) : ℝ :=
  ell^2*B^4*F^2*primeProductNorm p x.firstDivisor/
    (K*(primeProductNorm p x.common)^2*globalCubeJNorm p x)

def globalSecondDelta (B F : ℝ) (x : GlobalSecondData ι) (side : Bool) : ℝ :=
  B*F*primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.firstCommon*
    primeProductNorm p (x.source.sourceCommon\x.source.divisor)

def globalNominalChildRow (K B F : ℝ) (x : GlobalSecondData ι) (side : Bool) : ℝ :=
  K*globalCubeJNorm p x/((globalSecondDelta p B F x side)^2*B^2)


include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCubeActiveRoot_pos (x : GlobalSecondData ι) : 0 < globalCubeActiveRoot p x := by
  have hh := element_norm_ge_one (∏ i∈cubeActiveSupport x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)
    (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))
  change 0 < ‖eisEmbedding _‖
  nlinarith [norm_nonneg (eisEmbedding (∏ i∈cubeActiveSupport x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i))]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstColumnScale_pos (ell : ℝ) (hell : 0 < ell) (x : GlobalSecondData ι) (side : Bool) :
    0 < globalFirstColumnScale p ell x side :=
  div_pos hell (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondDelta_ge (B F : ℝ) (hB : 0 ≤ B) (hF : 1 ≤ F) (x : GlobalSecondData ι) (side : Bool) :
    B ≤ globalSecondDelta p B F x side := by
  have hA := primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  have ht := primeProductNorm_ge_one p hp x.firstCommon
  have hR := primeProductNorm_ge_one p hp (x.source.sourceCommon\x.source.divisor)
  unfold globalSecondDelta
  calc
    B = B*1*1*1*1 := by ring
    _ ≤ _ := by gcongr

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondDelta_pos (B F : ℝ) (hB : 0 < B) (hF : 0 < F) (x : GlobalSecondData ι) (side : Bool) :
    0 < globalSecondDelta p B F x side := by
  unfold globalSecondDelta
  exact mul_pos (mul_pos (mul_pos (mul_pos hB hF)
    (FirstPassCubeLabels.primeProductNorm_pos p hp _))
    (FirstPassCubeLabels.primeProductNorm_pos p hp _)) (FirstPassCubeLabels.primeProductNorm_pos p hp _)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalBaseLabel_norm (x : GlobalSecondData ι) :
    ‖eisEmbedding (secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent
      x.cube.leftBit x.cube.rightBit)‖^2 = primeProductNorm p x.common*globalCubeJNorm p x := by
  simp only [secondBaseLabel,map_mul,norm_mul,mul_pow,primeSubsetGenerator_norm_eq_productNorm,globalCubeJNorm]


include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecond_child_mass (ell B F : ℝ) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F)
    (x : GlobalSecondData ι) (side : Bool) (j : SecondLogIndex) :
    secondLogX p (x.source.sourceCommon\x.source.divisor)
      (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) j *
      secondLogLabelBound p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent
        x.cube.leftBit x.cube.rightBit j =
    Real.exp 2*((ell*B^3)*F*globalCubeJNorm p x/(globalSecondDelta p B F x side*B^2)) := by
  rw [secondLogX_label_cost,globalBaseLabel_norm]
  have hC := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).ne'
  have ha := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
  have ht := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).ne'
  have hr := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).ne'
  unfold globalFirstColumnScale globalSecondDelta
  field_simp


end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalChildMass (ell : ℝ) (x : GlobalSecondData ι) (side : Bool) (j : SecondLogIndex) : ℝ :=
  secondLogX p (x.source.sourceCommon\x.source.divisor)
    (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) j *
    secondLogLabelBound p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent
      x.cube.leftBit x.cube.rightBit j


end

theorem ceil_strict_of_half {a b : ℝ} (hb : 2 ≤ b) (ha : a ≤ b/2) : ⌈a⌉₊ < ⌈b⌉₊ := by
  have hc : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
  have hn : 2 ≤ ⌈b⌉₊ := by exact_mod_cast (hb.trans hc)
  have hn1 : 1 ≤ ⌈b⌉₊ := by omega
  have hbound : a ≤ ((⌈b⌉₊-1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn1,Nat.cast_one]
    have hh : (2 : ℝ) ≤ ⌈b⌉₊ := by exact_mod_cast hn
    linarith
  have hf : ⌈a⌉₊ ≤ ⌈b⌉₊-1 := Nat.ceil_le.mpr hbound
  omega


end SecondPassArithmetic

end

end OAI

end



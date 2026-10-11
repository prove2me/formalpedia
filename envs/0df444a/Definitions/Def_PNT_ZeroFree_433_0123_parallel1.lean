-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0123_parallel1
-- name    : PNT_ZeroFree_433_0123_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:15:33.152904+00:00
-- url     : https://prove2.me/theorems/ee6a1268-9a40-471c-98fd-c686b369c12d
-- title:
--   Zero-free region foundations: QuadraticSieve.HighKernelGeometry [0123_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.HighKernelGeometry
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/HighKernelGeometry.lean#L189-L614

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0015
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0144_parallel1
import Definitions.Def_PNT_ZeroFree_433_0185_parallel1
import Definitions.Def_PNT_ZeroFree_433_0192_parallel1
import Definitions.Def_PNT_ZeroFree_433_0215_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0221_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel1
import Definitions.Def_PNT_ZeroFree_433_0231_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/HighKernelGeometry.lean
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

open scoped BigOperators Classical


namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

def bottomRowUnitary (c d : ℂ) (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![star d/(r:ℂ),-star c/(r:ℂ);c/(r:ℂ),d/(r:ℂ)]

lemma bottomRowUnitary_mem (c d : ℂ) (r : ℝ) (hr : r≠0)
    (hrow : ‖c‖^2+‖d‖^2=r^2) : bottomRowUnitary c d r∈Matrix.unitaryGroup (Fin 2) ℂ := by
  have hC : c*star c+d*star d=(r:ℂ)^2 := by
    simpa only [Complex.ofReal_add,Complex.ofReal_pow,← Complex.mul_conj',Complex.star_def] using
      congrArg (fun x : ℝ => (x:ℂ)) hrow
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr
  simp only [Complex.star_def] at hC
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bottomRowUnitary,Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply,
      Complex.conj_ofReal] <;>
    field_simp [hrC] <;> first | exact hC | (simpa only [mul_comm,add_comm] using hC) | ring

lemma iwasawa_z_row_identities (a b c d : ℂ) (q : ℝ)
    (hq : q≠0) (hrow : (q:ℂ)=c*star c+d*star d) (hdet : a*d-b*c=1) :
    star d/(q:ℂ)+(a*star c+b*star d)/(q:ℂ)*c=a ∧
    -star c/(q:ℂ)+(a*star c+b*star d)/(q:ℂ)*d=b := by
  have hqC : (q:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hq
  constructor
  · field_simp [hqC]
    rw [hrow]
    linear_combination -(star d)*hdet
  · field_simp [hqC]
    rw [hrow]
    linear_combination (star c)*hdet

def matrixHorizontal (g : SL(2,ℂ)) : ℂ :=
  (g 0 0*star (g 1 0)+g 0 1*star (g 1 1))/(rowEnergy (complexBottomRow g):ℂ)

lemma matrix_iwasawa_factor (g : SL(2,ℂ)) :
    ∃k : SL(2,ℂ), k∈compactSubgroup ∧
      g=upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g)*k := by
  let q : ℝ := rowEnergy (complexBottomRow g)
  let r : ℝ := Real.sqrt q
  have hq : 0<q := rowEnergy_pos _ (complexBottomRow_ne_zero g)
  have hr : 0<r := Real.sqrt_pos.mpr hq
  have hr2 : r^2=q := Real.sq_sqrt hq.le
  have hrow : ‖g 1 0‖^2+‖g 1 1‖^2=r^2 := by
    rw [hr2]
    rfl
  have hqC : (q:ℂ)=g 1 0*star (g 1 0)+g 1 1*star (g 1 1) := by
    simp only [q,rowEnergy,complexBottomRow,Complex.ofReal_add,Complex.ofReal_pow,
      ← Complex.mul_conj',Complex.star_def]
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  have hz := iwasawa_z_row_identities (g 0 0) (g 0 1) (g 1 0) (g 1 1) q hq.ne' hqC hdet
  let B := upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g)
  let U := bottomRowUnitary (g 1 0) (g 1 1) r
  have hroot : Real.sqrt (liftedHeight g)=r⁻¹ := by
    exact Real.sqrt_inv q
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hqrC : (r:ℂ)^2=(q:ℂ) := by exact_mod_cast hr2
  have hB : (B:Matrix (Fin 2) (Fin 2) ℂ)=
      !![(r:ℂ)⁻¹,matrixHorizontal g*(r:ℂ);0,(r:ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B,upperSection,hroot,Complex.ofReal_inv,div_eq_mul_inv]
  have hfactor : (B:Matrix (Fin 2) (Fin 2) ℂ)*U=(g:Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hB]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp only [Matrix.mul_apply,Fin.sum_univ_two]
    · change (r:ℂ)⁻¹*(star (g 1 1)/(r:ℂ))+(matrixHorizontal g*(r:ℂ))*(g 1 0/(r:ℂ))=g 0 0
      calc
        _ = star (g 1 1)/(q:ℂ)+matrixHorizontal g*g 1 0 := by
          rw [← hqrC]
          field_simp [hrC]
        _ = _ := hz.1
    · change (r:ℂ)⁻¹*(-star (g 1 0)/(r:ℂ))+(matrixHorizontal g*(r:ℂ))*(g 1 1/(r:ℂ))=g 0 1
      calc
        _ = -star (g 1 0)/(q:ℂ)+matrixHorizontal g*g 1 1 := by
          rw [← hqrC]
          field_simp [hrC]
        _ = _ := hz.2
    · change 0*(star (g 1 1)/(r:ℂ))+(r:ℂ)*(g 1 0/(r:ℂ))=g 1 0
      field_simp [hrC] ; ring
    · change 0*(-star (g 1 0)/(r:ℂ))+(r:ℂ)*(g 1 1/(r:ℂ))=g 1 1
      field_simp [hrC] ; ring
  let k : SL(2,ℂ) := B⁻¹*g
  have hk : (k:Matrix (Fin 2) (Fin 2) ℂ)=U := by
    change ((B⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ) * (g:Matrix (Fin 2) (Fin 2) ℂ)=U
    rw [← hfactor,← Matrix.mul_assoc]
    have hi : ((B⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*(B:Matrix (Fin 2) (Fin 2) ℂ)=1 := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_one] using
        congrArg (fun M : SL(2,ℂ) => (M:Matrix (Fin 2) (Fin 2) ℂ)) (inv_mul_cancel B)
    rw [hi,Matrix.one_mul]
  refine ⟨k,?_,?_⟩
  · change (k:Matrix (Fin 2) (Fin 2) ℂ)∈Matrix.unitaryGroup (Fin 2) ℂ
    rw [hk]
    exact bottomRowUnitary_mem _ _ r hr.ne' hrow
  · dsimp [k,B]
    group

theorem upperPoint_surjective (w : HyperbolicSpace) :
    ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v, upperPoint z v hv=w := by
  induction w using Quotient.inductionOn with
  | _ g =>
    obtain ⟨k,hk,hg⟩ := matrix_iwasawa_factor g
    refine ⟨matrixHorizontal g,liftedHeight g,liftedHeight_pos g,?_⟩
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    change (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*g∈compactSubgroup
    have hcancel : (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*g=k := by
      calc
        _ = (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*
            (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g)*k) :=
          congrArg (fun M => (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*M) hg
        _ = k := inv_mul_cancel_left _ _
    rw [hcancel]
    exact hk

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O

lemma eisEmbedding_range_closed : IsClosed (Set.range eisEmbedding) := by
  let : DiscreteTopology periodLattice := by unfold periodLattice; infer_instance
  have hc : IsClosed (periodLattice : Set ℂ) :=
    AddSubgroup.isClosed_of_discrete (H := periodLattice.toAddSubgroup)
  have heq : Set.range eisEmbedding=(fun z : ℂ => 3*z) ⁻¹' (periodLattice : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨n,rfl⟩
      exact three_embedding_mem n
    · intro hz
      obtain ⟨n,hn⟩ := periodPoint_bijective.2 ⟨3*z,hz⟩
      refine ⟨n,?_⟩
      have h := congrArg Subtype.val hn
      exact mul_left_cancel₀ (by norm_num : (3:ℂ)≠0) h
  rw [heq]
  exact hc.preimage (by fun_prop)

lemma exists_nearest_eisenstein (z : ℂ) :
    ∃n : O, ∀m : O, ‖z-eisEmbedding n‖≤‖z-eisEmbedding m‖ := by
  obtain ⟨y,hy,heq⟩ := eisEmbedding_range_closed.exists_infDist_eq_dist
    (Set.range_nonempty eisEmbedding) z
  obtain ⟨n,rfl⟩ := hy
  refine ⟨n,fun m => ?_⟩
  rw [← dist_eq_norm,← dist_eq_norm,← heq]
  exact Metric.infDist_le_dist_of_mem ⟨m,rfl⟩

lemma hexagon_norm_sq_bound (x y : ℝ)
    (hx : |x|≤1/2)
    (h₁ : x+Real.sqrt 3*y≤1) (h₂ : x-Real.sqrt 3*y≤1)
    (h₃ : -x+Real.sqrt 3*y≤1) (h₄ : -x-Real.sqrt 3*y≤1) :
    x^2+y^2≤1/3 := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have ha : |x|+Real.sqrt 3*|y|≤1 := by
    rcases le_total 0 x with hxx | hxx <;> rcases le_total 0 y with hyy | hyy
    · simpa only [abs_of_nonneg hxx,abs_of_nonneg hyy] using h₁
    · simpa only [abs_of_nonneg hxx,abs_of_nonpos hyy,mul_neg,← sub_eq_add_neg] using h₂
    · simpa only [abs_of_nonpos hxx,abs_of_nonneg hyy] using h₃
    · simpa only [abs_of_nonpos hxx,abs_of_nonpos hyy,mul_neg,← sub_eq_add_neg] using h₄
  have hyprod : 0≤(1-|x|-Real.sqrt 3*|y|)*(1-|x|+Real.sqrt 3*|y|) := by
    apply mul_nonneg
    · linarith
    · have : 0≤Real.sqrt 3*|y| := mul_nonneg (Real.sqrt_nonneg 3) (abs_nonneg y)
      linarith
  have hxprod : |x| * (2*|x|-1)≤0 := mul_nonpos_of_nonneg_of_nonpos (abs_nonneg x) (by linarith)
  have hxy : (Real.sqrt 3*|y|)^2=3*y^2 := by rw [mul_pow,hs,sq_abs]
  nlinarith [sq_abs x,sq_abs y]

theorem exists_eisenstein_distance_sq_le_third (z : ℂ) :
    ∃n : O, Complex.normSq (z-eisEmbedding n)≤1/3 := by
  obtain ⟨n,hn⟩ := exists_nearest_eisenstein z
  let w := z-eisEmbedding n
  have hmin (u : O) : Complex.normSq w≤Complex.normSq (w-eisEmbedding u) := by
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq]
    apply pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    have h := hn (n+u)
    simpa only [map_add,sub_add_eq_sub_sub] using h
  have hre : omega3.re= -(1/2:ℝ) := by norm_num [omega3]
  have h1 := hmin 1
  have hn1 := hmin (-1)
  have hω := hmin (ActualEisensteinCoordinates.eval 0 1)
  have hnω := hmin (-(ActualEisensteinCoordinates.eval 0 1))
  have hη := hmin (ActualEisensteinCoordinates.eval 1 1)
  have hnη := hmin (-(ActualEisensteinCoordinates.eval 1 1))
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  simp only [map_one,map_neg,eisEmbedding_eval,Int.cast_zero,Int.cast_one,zero_add,one_mul,
    Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.neg_re,Complex.neg_im,Complex.one_re,Complex.one_im,hre,omega3_im] at h1 hn1 hω hnω hη hnη
  refine ⟨n,?_⟩
  change Complex.normSq w≤1/3
  rw [Complex.normSq_apply,← sq,← sq]
  apply hexagon_norm_sq_bound
  · apply abs_le.mpr
    constructor <;> nlinarith
  · nlinarith [hη]
  · nlinarith [hnω]
  · nlinarith [hω]
  · nlinarith [hnη]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def integralBottomRow (M : SL(2,O)) : Fin 2 → O := fun j => M 1 j
def integralRowEnergy (g : SL(2,ℂ)) (v : Fin 2 → O) : ℝ :=
  rowEnergy (rowOperator g (fun j => eisEmbedding (v j)))

lemma integralRowEnergy_sublevel_finite (g : SL(2,ℂ)) (C : ℝ) :
    Set.Finite {v : Fin 2 → O | integralRowEnergy g v≤C} := by
  have hb : Set.Finite (Metric.closedBall (0 : (Fin 2×Fin 2)→ℤ) (rowBound g*Real.sqrt C)) :=
    (isCompact_closedBall _ _).finite_of_discrete
  apply (Set.Finite.preimage rowCoordinates_injective.injOn hb).subset
  intro v hv
  change rowCoordinates v∈Metric.closedBall 0 (rowBound g*Real.sqrt C)
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (coordinates_le_transformed_energy g v).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv) (rowBound_pos g).le)


end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def integralTranslation (n : O) : SL(2,O) :=
  ⟨!![1,n;0,1],by simp [Matrix.det_fin_two]⟩
def integralInversion : SL(2,O) :=
  ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩


def truncatedFordBox (T : ℝ) : Set (ℂ×ℝ) :=
  Metric.closedBall 0 1 ×ˢ Set.Icc (Real.sqrt (2/3)) T
lemma truncatedFordBox_isCompact (T : ℝ) : IsCompact (truncatedFordBox T) :=
  (isCompact_closedBall _ _).prod isCompact_Icc

lemma mem_truncatedFordBox (z : ℂ) (v T : ℝ)
    (hz : Complex.normSq z≤1/3) (hv : Real.sqrt (2/3)≤v) (hT : v≤T) :
    (z,v)∈truncatedFordBox T := by
  refine ⟨?_,hv,hT⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  rw [Complex.normSq_eq_norm_sq] at hz
  nlinarith [norm_nonneg z]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma levelThree_finiteIndex : levelThree.FiniteIndex := by
  let : Finite (O ⧸ Ideal.span {(3:O)}) := finite_quotient_span (by norm_num)
  unfold levelThree
  infer_instance

def finiteCubicMultiplier : levelThree →* rootsOfUnity 3 ℂ where
  toFun M := rootsOfUnity.mkOfPowEq (complexCharacter M) (complexCharacter_cube M)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    simp only [rootsOfUnity.coe_mkOfPowEq,map_one,OneMemClass.coe_one,Units.val_one]
  map_mul' M N := by
    apply Subtype.ext
    apply Units.ext
    simp only [rootsOfUnity.coe_mkOfPowEq,map_mul,Subgroup.coe_mul,Units.val_mul]

def globalKubotaKernel : Subgroup (SL(2,O)) := finiteCubicMultiplier.ker.map levelThree.subtype

lemma globalKubotaKernel_finiteIndex : globalKubotaKernel.FiniteIndex := by
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  let : finiteCubicMultiplier.ker.FiniteIndex := inferInstance
  constructor
  rw [globalKubotaKernel,Subgroup.index_map_subtype]
  exact mul_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := finiteCubicMultiplier.ker))
    (Subgroup.FiniteIndex.index_ne_zero (H := levelThree))

@[simp] lemma finiteCubicMultiplier_coe (M : levelThree) :
    ((finiteCubicMultiplier M : ℂˣ) : ℂ)=complexCharacter M := rfl

lemma finiteCubicMultiplier_eq_one (M : levelThree) :
    finiteCubicMultiplier M=1 ↔ complexCharacter M=1 := by
  constructor
  · intro h
    have hc := congrArg (fun x : rootsOfUnity 3 ℂ => ((x:ℂˣ):ℂ)) h
    simpa only [finiteCubicMultiplier_coe,OneMemClass.coe_one,Units.val_one] using hc
  · intro h
    apply Subtype.ext
    apply Units.ext
    simpa only [finiteCubicMultiplier_coe,OneMemClass.coe_one,Units.val_one] using h

lemma globalKubotaKernel_mem (M : SL(2,O)) :
    M∈globalKubotaKernel ↔ ∃hM : M∈levelThree,complexCharacter ⟨M,hM⟩=1 := by
  constructor
  · rintro ⟨N,hN,hNM⟩
    subst M
    exact ⟨N.property,(finiteCubicMultiplier_eq_one N).mp hN⟩
  · rintro ⟨hM,hc⟩
    exact ⟨⟨M,hM⟩,(finiteCubicMultiplier_eq_one ⟨M,hM⟩).mpr hc,rfl⟩

lemma finite_right_representatives {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] :
    ∃S : Finset G, ∀g : G,∃r∈S,r⁻¹*g∈H := by
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  let S : Finset G := Finset.univ.image (fun q : G ⧸ H => Quotient.out q)
  refine ⟨S,fun g => ?_⟩
  let q : G ⧸ H := QuotientGroup.mk g
  refine ⟨Quotient.out q,?_,?_⟩
  · exact Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩
  · exact QuotientGroup.leftRel_apply.mp (Quotient.exact' (Quotient.out_eq' q))


end CubicEisenstein

end

end OAI

end



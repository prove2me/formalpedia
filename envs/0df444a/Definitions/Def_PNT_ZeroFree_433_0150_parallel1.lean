-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0150_parallel1
-- name    : PNT_ZeroFree_433_0150_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:54:01.482282+00:00
-- url     : https://prove2.me/theorems/237cb3db-4ec2-4450-b60c-5203b86904d0
-- title:
--   Zero-free region foundations: CubicSieve.RowCaps [0150_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.RowCaps
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/RowCaps.lean#L82-L548

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0061
import Definitions.Def_PNT_ZeroFree_433_0100
import Definitions.Def_PNT_ZeroFree_433_0103
import Definitions.Def_PNT_ZeroFree_433_0104
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0149_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229
import Definitions.Def_PNT_ZeroFree_433_0258_parallel1
import Definitions.Def_PNT_ZeroFree_433_0262
import Definitions.Def_PNT_ZeroFree_433_0506

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/RowCaps.lean
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
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

def globalFirstRowCap (K ell B F : ℝ) : ℝ :=
  (Real.exp 1)^2*ell^2*B^6*F^2/K

theorem globalFirstRowCap_pos (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) :
    0<globalFirstRowCap K ell B F := by
  unfold globalFirstRowCap
  positivity

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]


end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)


end SecondPassArithmetic

open scoped BigOperators Classical
namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets

noncomputable abbrev actualSextic := ActualEisensteinCubic.canonicalSextic

def exceptionalPiece (P : Ideal O) [P.IsMaximal] (e : Fin 3) (n b : O) : ℂ :=
  if e=0 then -(rootCard (O ⧸ P) : ℂ)⁻¹
  else if e=1 then (rootCard (O ⧸ P) : ℂ)*(if n∈P then 1 else 0)
  else (rootCard (O ⧸ P) : ℂ)*(if n∉P ∧ b∈P then 1 else 0)

theorem bracket_four_eq_sum_exceptionalPiece (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (n b : O) :
    bracket (actualSextic P hg) 4 (Ideal.Quotient.mk P (n*b^3)) =
      ∑e : Fin 3, exceptionalPiece P e n b := by
  rw [canonical_bracket_four_cube_split]
  simp [Fin.sum_univ_succ,exceptionalPiece]
  ring

def exceptionalBranch {ι : Type*} [Fintype ι] (P : ι→Ideal O)
    [∀i,(P i).IsMaximal] (e : ι→Fin 3) (n b : O) : ℂ :=
  ∏i, exceptionalPiece (P i) (e i) n b

theorem prod_bracket_four_eq_branches {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (n b : O) :
    (∏i,bracket (actualSextic (P i) (hg i)) 4 (Ideal.Quotient.mk (P i) (n*b^3))) =
      ∑e : ι→Fin 3, exceptionalBranch P e n b := by
  simp_rw [bracket_four_eq_sum_exceptionalPiece]
  simpa only [Fintype.piFinset_univ,exceptionalBranch] using
    Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset (Fin 3)))
      (fun i e => exceptionalPiece (P i) e n b)

def exceptionalDivisor {ι : Type*} [Fintype ι] (P : ι→Ideal O)
    (e : ι→Fin 3) (v : Fin 3) : Ideal O := ∏i, if e i=v then P i else 1

theorem exceptionalBranch_support {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (e : ι→Fin 3) (n b : O)
    (hne : exceptionalBranch P e n b≠0) :
    (∀i,e i=1 → n∈P i) ∧ (∀i,e i=2 → n∉P i ∧ b∈P i) := by
  have hn i : exceptionalPiece (P i) (e i) n b≠0 :=
    (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
  constructor
  · intro i hi
    by_contra h
    exact hn i (by simp [exceptionalPiece,hi,h])
  · intro i hi
    by_contra h
    exact hn i (by simp [exceptionalPiece,hi,h])

theorem exceptionalBranch_divisibility {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (e : ι→Fin 3) (n b : O) (hne : exceptionalBranch P e n b≠0) :
    exceptionalDivisor P e 1 ∣ Ideal.span {n} ∧
    exceptionalDivisor P e 2 ∣ Ideal.span {b} ∧
    (∀i,e i=2 → n∉P i) := by
  have hs := exceptionalBranch_support P e n b hne
  have hprod (v : Fin 3) (z : O) (hz : ∀i,e i=v → z∈P i) :
      exceptionalDivisor P e v ∣ Ideal.span {z} := by
    rw [exceptionalDivisor]
    apply Fintype.prod_dvd_of_coprime
    · intro i j hij
      change IsCoprime (if e i=v then P i else 1) (if e j=v then P j else 1)
      by_cases hi : e i=v
      · rw [if_pos hi]
        by_cases hj : e j=v
        · rw [if_pos hj]
          exact hcop hij
        · rw [if_neg hj]
          exact isCoprime_one_right
      · rw [if_neg hi]
        exact isCoprime_one_left
    · intro i
      split_ifs with hi
      · rw [Ideal.dvd_iff_le,Ideal.span_le,Set.singleton_subset_iff,SetLike.mem_coe]
        exact hz i hi
      · exact one_dvd _
  exact ⟨hprod 1 n hs.1,hprod 2 b (fun i hi => (hs.2 i hi).2),fun i hi => (hs.2 i hi).1⟩

theorem rootCard_eq_sqrt_absNorm (P : Ideal O) [P.IsMaximal] :
    rootCard (O ⧸ P)=Real.sqrt (Ideal.absNorm P:ℝ) := by
  rw [rootCard,←Nat.card_eq_fintype_card]
  rfl

def exceptionalSize {ι : Type*} [Fintype ι] (P : ι→Ideal O)
    [∀i,(P i).IsMaximal] (e : ι→Fin 3) : ℝ :=
  ∏i, if e i=0 then (rootCard (O ⧸ P i))⁻¹ else rootCard (O ⧸ P i)

theorem exceptionalPiece_norm_le (P : Ideal O) [P.IsMaximal]
    (e : Fin 3) (n b : O) :
    ‖exceptionalPiece P e n b‖≤(if e=0 then (rootCard (O ⧸ P))⁻¹ else rootCard (O ⧸ P)) := by
  have hr : 0≤rootCard (O ⧸ P) := rootCard_pos.le
  fin_cases e <;> simp only [exceptionalPiece,Fin.isValue,Fin.zero_eta,↓reduceIte]
  · simp [abs_of_nonneg hr]
  · by_cases hn : n∈P <;> simp [hn,abs_of_nonneg hr,hr]
  · by_cases hn : n∉P ∧ b∈P <;> simp [hn,abs_of_nonneg hr,hr]

theorem exceptionalBranch_norm_le {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (e : ι→Fin 3) (n b : O) :
    ‖exceptionalBranch P e n b‖≤exceptionalSize P e := by
  rw [exceptionalBranch,norm_prod,exceptionalSize]
  exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => exceptionalPiece_norm_le _ _ _ _)

theorem exceptionalDivisor_ne_zero {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (hp : ∀i,P i≠0) (e : ι→Fin 3) (v : Fin 3) :
    exceptionalDivisor P e v≠0 := by
  rw [exceptionalDivisor]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  split_ifs
  · exact hp i
  · exact one_ne_zero

theorem sqrt_norm_exceptionalDivisor {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (e : ι→Fin 3) (v : Fin 3) :
    Real.sqrt (Ideal.absNorm (exceptionalDivisor P e v):ℝ)=
      ∏i,if e i=v then rootCard (O ⧸ P i) else 1 := by
  rw [exceptionalDivisor,map_prod,Nat.cast_prod,Real.sqrt_prod]
  · apply Finset.prod_congr rfl
    intro i _
    split_ifs with hi
    · rw [rootCard_eq_sqrt_absNorm]
    · simp
  · intro i _
    exact Nat.cast_nonneg _

theorem exceptionalSize_eq {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (e : ι→Fin 3) :
    exceptionalSize P e=
      Real.sqrt (Ideal.absNorm (exceptionalDivisor P e 1):ℝ)*
      Real.sqrt (Ideal.absNorm (exceptionalDivisor P e 2):ℝ)/
      Real.sqrt (Ideal.absNorm (exceptionalDivisor P e 0):ℝ) := by
  rw [sqrt_norm_exceptionalDivisor,sqrt_norm_exceptionalDivisor,sqrt_norm_exceptionalDivisor,
    ←Finset.prod_mul_distrib,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  generalize e i=x
  fin_cases x <;> simp

theorem exceptional_normalized_bound {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hp : ∀i,P i≠0)
    (e : ι→Fin 3) (n b : O) (U B : ℝ) (hU : 0<U) (hB : 0<B) :
    ‖exceptionalBranch P e n b‖ /
      (Real.sqrt ((Ideal.absNorm (exceptionalDivisor P e 1):ℝ)*U)*
        ((Ideal.absNorm (exceptionalDivisor P e 2):ℝ)*B)) ≤
      1/(Real.sqrt U*B*Real.sqrt ((Ideal.absNorm (exceptionalDivisor P e 0):ℝ)*
        (Ideal.absNorm (exceptionalDivisor P e 2):ℝ))) := by
  have hn (v : Fin 3) : 0<(Ideal.absNorm (exceptionalDivisor P e v):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => exceptionalDivisor_ne_zero P hp e v (Ideal.absNorm_eq_zero_iff.mp hz))
  have hs (v : Fin 3) : 0<Real.sqrt (Ideal.absNorm (exceptionalDivisor P e v):ℝ) := Real.sqrt_pos.mpr (hn v)
  have hsu : 0<Real.sqrt U := Real.sqrt_pos.mpr hU
  apply (div_le_div_of_nonneg_right (exceptionalBranch_norm_le P e n b) (by positivity)).trans
  rw [exceptionalSize_eq,Real.sqrt_mul (hn 1).le,Real.sqrt_mul (hn 0).le]
  have he := Real.sq_sqrt (hn 2).le
  apply le_of_eq
  field_simp [(hs 0).ne', (hs 1).ne', (hs 2).ne', (hn 2).ne', hsu.ne', hB.ne']
  nlinarith

end CompletedGauss


open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff

namespace CubicEisenstein

def spatialHorizontal (p : SpatialCoordinates) : ℂ := (p 0:ℂ)+(p 1:ℂ)*Complex.I

def mobiusSpatialDenominator (g : SL(2,ℂ)) (p : SpatialCoordinates) : ℝ :=
  Complex.normSq (g 1 0*spatialHorizontal p+g 1 1)+Complex.normSq (g 1 0)*(p 2)^2

def mobiusSpatialHorizontal (g : SL(2,ℂ)) (p : SpatialCoordinates) : ℂ :=
  ((g 0 0*spatialHorizontal p+g 0 1)*star (g 1 0*spatialHorizontal p+g 1 1)+
    g 0 0*star (g 1 0)*(p 2:ℂ)^2)/(mobiusSpatialDenominator g p:ℂ)

def mobiusSpatial (g : SL(2,ℂ)) (p : SpatialCoordinates) : SpatialCoordinates :=
  ![(mobiusSpatialHorizontal g p).re,(mobiusSpatialHorizontal g p).im,
    p 2/mobiusSpatialDenominator g p]

lemma mobiusSpatialDenominator_pos (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    0<mobiusSpatialDenominator g p := by
  simpa only [mobiusSpatialDenominator,Complex.normSq_eq_norm_sq] using
    mobius_denominator_pos g (spatialHorizontal p) (p 2) hp

lemma mobiusSpatial_positive (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    0<mobiusSpatial g p 2 := div_pos hp (mobiusSpatialDenominator_pos g p hp)


lemma spatialHorizontal_contDiff : ContDiff ℝ ∞ spatialHorizontal := by
  unfold spatialHorizontal
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)).add
    ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).mul contDiff_const)

lemma mobiusSpatialDenominator_contDiff (g : SL(2,ℂ)) : ContDiff ℝ ∞ (mobiusSpatialDenominator g) := by
  unfold mobiusSpatialDenominator
  have hz : ContDiff ℝ ∞ (fun p => g 1 0*spatialHorizontal p+g 1 1) :=
    (contDiff_const.mul spatialHorizontal_contDiff).add contDiff_const
  have hre := Complex.reCLM.contDiff.comp hz
  have him := Complex.imCLM.contDiff.comp hz
  change ContDiff ℝ ∞ (fun p =>
    (g 1 0*spatialHorizontal p+g 1 1).re*(g 1 0*spatialHorizontal p+g 1 1).re+
    (g 1 0*spatialHorizontal p+g 1 1).im*(g 1 0*spatialHorizontal p+g 1 1).im+
    Complex.normSq (g 1 0)*(p 2)^2)
  exact ((hre.mul hre).add (him.mul him)).add (contDiff_const.mul ((contDiff_apply ℝ ℝ 2).pow 2))

lemma mobiusSpatial_contDiffAt (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (mobiusSpatial g) p := by
  have hD := (mobiusSpatialDenominator_contDiff g).contDiffAt (x := p)
  have hDc : ContDiffAt ℝ ∞ (fun p => (mobiusSpatialDenominator g p:ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p hD
  have hnum : ContDiffAt ℝ ∞ (fun p : SpatialCoordinates =>
      (g 0 0*spatialHorizontal p+g 0 1)*star (g 1 0*spatialHorizontal p+g 1 1)+
        g 0 0*star (g 1 0)*(p 2:ℂ)^2) p := by
    have hz := spatialHorizontal_contDiff.contDiffAt (x := p)
    have hcz : ContDiffAt ℝ ∞ (fun p => g 1 0*spatialHorizontal p+g 1 1) p :=
      (contDiffAt_const.mul hz).add contDiffAt_const
    have hc := Complex.conjCLE.contDiff.contDiffAt.comp p hcz
    have hv : ContDiffAt ℝ ∞ (fun p : SpatialCoordinates => (p 2:ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiff_apply ℝ ℝ 2).contDiffAt
    exact (((contDiffAt_const.mul hz).add contDiffAt_const).mul hc).add
      (contDiffAt_const.mul (hv.pow 2))
  have hh : ContDiffAt ℝ ∞ (mobiusSpatialHorizontal g) p :=
    by
      unfold mobiusSpatialHorizontal
      simp only [div_eq_mul_inv]
      exact hnum.mul (hDc.inv (Complex.ofReal_ne_zero.mpr (mobiusSpatialDenominator_pos g p hp).ne'))
  apply contDiffAt_pi.mpr
  intro j
  fin_cases j
  · exact Complex.reCLM.contDiff.contDiffAt.comp p hh
  · exact Complex.imCLM.contDiff.contDiffAt.comp p hh
  · exact (by fun_prop : ContDiffAt ℝ ∞ (fun p : SpatialCoordinates => p 2) p).div hD
      (mobiusSpatialDenominator_pos g p hp).ne'

abbrev PositiveSpatial := {p : SpatialCoordinates // 0<p 2}

def positiveSpatialToUpper (p : PositiveSpatial) : UpperCoordinates :=
  ⟨(spatialHorizontal p.1,p.1 2),p.2⟩
def upperToPositiveSpatial (p : UpperCoordinates) : PositiveSpatial :=
  ⟨![p.1.1.re,p.1.1.im,p.1.2],p.2⟩

lemma positiveSpatialToUpper_continuous : Continuous positiveSpatialToUpper := by
  apply Continuous.subtype_mk
  exact (spatialHorizontal_contDiff.continuous.comp continuous_subtype_val).prodMk
    ((continuous_apply 2).comp continuous_subtype_val)
lemma upperToPositiveSpatial_continuous : Continuous upperToPositiveSpatial := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  fin_cases j <;> fun_prop

def positiveSpatialUpperHomeomorph : PositiveSpatial ≃ₜ UpperCoordinates where
  toFun := positiveSpatialToUpper
  invFun := upperToPositiveSpatial
  left_inv p := by
    apply Subtype.ext
    funext j
    fin_cases j <;> simp [upperToPositiveSpatial,positiveSpatialToUpper,spatialHorizontal]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact Complex.re_add_im _
    · rfl
  continuous_toFun := positiveSpatialToUpper_continuous
  continuous_invFun := upperToPositiveSpatial_continuous


end CubicEisenstein


end

end OAI

end



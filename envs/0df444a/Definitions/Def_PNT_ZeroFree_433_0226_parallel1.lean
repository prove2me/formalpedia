-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0226_parallel1
-- name    : PNT_ZeroFree_433_0226_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:46:43.683891+00:00
-- url     : https://prove2.me/theorems/8e04906c-3a9c-4fd4-8e24-16beacbdbd20
-- title:
--   Zero-free region foundations: Eisenstein.ResidualFourierExpansion [0226_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.ResidualFourierExpansion
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ResidualFourierExpansion.lean#L213-L628

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0118_parallel1
import Definitions.Def_PNT_ZeroFree_433_0122_parallel1
import Definitions.Def_PNT_ZeroFree_433_0123_parallel1
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0127_parallel2
import Definitions.Def_PNT_ZeroFree_433_0128_parallel1
import Definitions.Def_PNT_ZeroFree_433_0129_parallel1
import Definitions.Def_PNT_ZeroFree_433_0135_parallel1
import Definitions.Def_PNT_ZeroFree_433_0137_parallel2
import Definitions.Def_PNT_ZeroFree_433_0181_parallel1
import Definitions.Def_PNT_ZeroFree_433_0208_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ResidualFourierExpansion.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace CubicEisenstein

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
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal Pointwise MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota

lemma periodDomain_memLp_of_continuous (f : ℂ→ℂ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict periodDomain) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable.restrict).mpr
  apply (((hf.norm.pow 2).continuousOn).integrableOn_compact
    (isCompact_closedBall (0:ℂ) (∑i,‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz

lemma upperTranslation_mem_kernel (n : ActualEisensteinCubic.O) :
    (upperTranslation n : SL(2,ActualEisensteinCubic.O))∈globalKubotaKernel := by
  exact (globalKubotaKernel_mem _).mpr
    ⟨(upperTranslation n).property,complexCharacter_upperTranslation n⟩

lemma kernelProjection_upper_period (v : ℝ) (hv : 0<v) (z : ℂ) (n : ActualEisensteinCubic.O) :
    integralOrbitProjection globalKubotaKernel (upperPoint (z+3*eisEmbedding n) v hv)=
      integralOrbitProjection globalKubotaKernel (upperPoint z v hv) := by
  let M : globalKubotaKernel := ⟨upperTranslation n,upperTranslation_mem_kernel n⟩
  have ha : integralComplexMatrix (M:SL(2,ActualEisensteinCubic.O)) • upperPoint z v hv=
      upperPoint (z+3*eisEmbedding n) v hv := by
    change (QuotientGroup.mk (complexMatrix (upperTranslation n)*upperSection z v hv) : HyperbolicSpace)=_
    rw [upperTranslation_section]
    rfl
  rw [←ha,integralOrbitProjection_eq]

lemma ae_eq_of_periodDomain_eq (f g : ℂ→ℂ)
    (hf : ∀(n : ActualEisensteinCubic.O)(z : ℂ),f (z+3*eisEmbedding n)=f z)
    (hg : ∀(n : ActualEisensteinCubic.O)(z : ℂ),g (z+3*eisEmbedding n)=g z)
    (he : f=ᵐ[volume.restrict periodDomain]g) : f=ᵐ[volume]g := by
  have hp (p : periodLattice) (z : ℂ) : f (p+ᵥz)=f z ∧ g (p+ᵥz)=g z := by
    obtain ⟨n,rfl⟩ := periodEquiv.surjective p
    change f (3*eisEmbedding n+z)=f z ∧ g (3*eisEmbedding n+z)=g z
    rw [add_comm]
    exact ⟨hf n z,hg n z⟩
  have hi : ∀p : periodLattice,p+ᵥ{z : ℂ | f z≠g z}={z : ℂ | f z≠g z} := by
    intro p
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change (f ((-p)+ᵥz)≠g ((-p)+ᵥz)) ↔ f z≠g z
    rw [(hp (-p) z).1,(hp (-p) z).2]
  have hz : volume ({z : ℂ | f z≠g z}∩periodDomain)=0 := by
    change ∀ᵐz ∂volume.restrict periodDomain,f z=g z at he
    rw [ae_restrict_iff' periodDomain_measurable] at he
    rw [ae_iff] at he
    have hs : {z : ℂ | f z≠g z}∩periodDomain =
        {z : ℂ | ¬(z∈periodDomain → f z=g z)} := by
      ext z
      simp only [Set.mem_ofPred_eq,Set.mem_inter_iff]
      tauto
    rw [hs]
    exact he
  change ∀ᵐz ∂volume,f z=g z
  rw [ae_iff]
  exact periodDomain_fundamental.measure_zero_of_invariant _ hi hz

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

lemma positive_height_interval_cover :
    Set.Ioi (0:ℝ) = ⋃n : ℕ,Set.Icc (1/((n:ℝ)+1)) ((n:ℝ)+1) := by
  ext v
  constructor
  · intro hv
    obtain ⟨n,hn⟩ := exists_nat_gt (max v (1/v))
    have hN : 0<(n:ℝ)+1 := by positivity
    have hvp : 0<v := hv
    have hvN : v≤(n:ℝ)+1 := by linarith [le_max_left v (1/v)]
    have hinv : 1/v≤(n:ℝ)+1 := by linarith [le_max_right v (1/v)]
    have hlow : 1/((n:ℝ)+1)≤v := by
      apply (div_le_iff₀ hN).mpr
      have hh := (div_le_iff₀ hvp).mp hinv
      nlinarith
    exact Set.mem_iUnion.mpr ⟨n,hlow,hvN⟩
  · intro hv
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hv
    exact lt_of_lt_of_le (by positivity : 0<(1:ℝ)/((n:ℝ)+1)) hn.1


end


open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def rationalUnipotent (t : ℤ) : SL(2,ℤ) :=
  ⟨!![1,t;0,1],by simp [Matrix.det_fin_two]⟩

lemma rationalUnipotent_add (a b : ℤ) :
    rationalUnipotent (a+b)=rationalUnipotent a*rationalUnipotent b := by
  apply Subtype.ext
  change (!![1,a+b;0,1] : Matrix (Fin 2) (Fin 2) ℤ) =
    (!![1,a;0,1] : Matrix (Fin 2) (Fin 2) ℤ) * !![1,b;0,1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,add_comm]

lemma rationalUnipotent_zero : rationalUnipotent 0=1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [rationalUnipotent]

lemma rationalUnipotent_neg (a : ℤ) : rationalUnipotent (-a)=(rationalUnipotent a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [←rationalUnipotent_add,neg_add_cancel,rationalUnipotent_zero]

lemma rationalUnipotent_one : rationalUnipotent 1=ModularGroup.T := rfl

lemma row_unipotent_conjugate (t : ℤ) (M : levelThree) :
    row (levelThreeConjugate (rationalEmbedding (rationalUnipotent (-t))) M)=
      Matrix.vecMul (row M) (rationalEmbedding (rationalUnipotent t):SL(2,ActualEisensteinCubic.O)) := by
  have hmap (u : ℤ) :
      (rationalEmbedding (rationalUnipotent u) : Matrix (Fin 2) (Fin 2) O) =
        !![1,(u : O);0,1] := by
    apply Matrix.ext
    intro i j
    change (Int.castRingHom O) ((!![1,u;0,1] : Matrix (Fin 2) (Fin 2) ℤ) i j) = _
    fin_cases i <;> fin_cases j <;> simp
  change ((rationalEmbedding (rationalUnipotent (-t)) * (M : SL(2,O)) *
      (rationalEmbedding (rationalUnipotent (-t)))⁻¹ : SL(2,O)) : Matrix (Fin 2) (Fin 2) O) 1 =
    Matrix.vecMul ((M : SL(2,O)) 1)
      (rationalEmbedding (rationalUnipotent t) : Matrix (Fin 2) (Fin 2) O)
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    hmap, Matrix.adjugate_fin_two]
  funext j
  fin_cases j <;> simp [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

def cuspUnipotentTranslate (t : ℤ) : CuspCosets→CuspCosets :=
  Quotient.map (fun M => levelThreeConjugate (rationalEmbedding (rationalUnipotent (-t))) M) (by
    intro M N h
    change row (levelThreeConjugate _ M)=row (levelThreeConjugate _ N)
    rw [row_unipotent_conjugate,row_unipotent_conjugate,show row M=row N from h])

lemma cuspUnipotentTranslate_inverse (t : ℤ) (x : CuspCosets) :
    cuspUnipotentTranslate (-t) (cuspUnipotentTranslate t x)=x := by
  induction x using Quotient.inductionOn with
  | _ M =>
    change cosetOf (levelThreeConjugate (rationalEmbedding (rationalUnipotent (- -t)))
      (levelThreeConjugate (rationalEmbedding (rationalUnipotent (-t))) M))=cosetOf M
    rw [←levelThreeConjugate_mul,←map_mul,←rationalUnipotent_add]
    simp only [neg_neg,add_neg_cancel,rationalUnipotent_zero,map_one,levelThreeConjugate_one]

def cuspUnipotentEquiv (t : ℤ) : CuspCosets≃CuspCosets where
  toFun := cuspUnipotentTranslate t
  invFun := cuspUnipotentTranslate (-t)
  left_inv := cuspUnipotentTranslate_inverse t
  right_inv x := by simpa only [neg_neg] using cuspUnipotentTranslate_inverse (-t) x

lemma cosetRow_cuspUnipotentEquiv (t : ℤ) (x : CuspCosets) :
    cosetRow (cuspUnipotentEquiv t x)=
      Matrix.vecMul (cosetRow x) (rationalEmbedding (rationalUnipotent t):SL(2,ActualEisensteinCubic.O)) := by
  induction x using Quotient.inductionOn with
  | _ M => exact row_unipotent_conjugate t M

lemma cosetCharacter_cuspUnipotentEquiv (t : ℤ) (x : CuspCosets) :
    cosetCharacter (cuspUnipotentEquiv t x)=cosetCharacter x := by
  induction x using Quotient.inductionOn with
  | _ M => exact complexCharacter_conjugate_rational (rationalUnipotent (-t)) M

lemma embeddedRow_cuspUnipotentEquiv (t : ℤ) (x : CuspCosets) :
    embeddedRow (cuspUnipotentEquiv t x)=
      Matrix.vecMul (embeddedRow x) (integralComplexMatrix (rationalEmbedding (rationalUnipotent t)):SL(2,ℂ)) := by
  funext j
  simp only [embeddedRow,Function.comp_def,cosetRow_cuspUnipotentEquiv,
    Matrix.vecMul,dotProduct,map_sum,map_mul,integralComplexMatrix_apply]

lemma summand_unipotent (t : ℤ) (g : SL(2,ℂ)) (s : ℂ) (x : CuspCosets) :
    summand (integralComplexMatrix (rationalEmbedding (rationalUnipotent t))*g) s x=
      summand g s (cuspUnipotentEquiv t x) := by
  rw [summand,summand,cosetCharacter_cuspUnipotentEquiv,
    embeddedRow_cuspUnipotentEquiv,←rowOperator_apply,rowOperator_mul]

theorem eisenstein_unipotent (t : ℤ) (g : SL(2,ℂ)) (s : ℂ) :
    eisenstein (integralComplexMatrix (rationalEmbedding (rationalUnipotent t))*g) s=eisenstein g s := by
  unfold eisenstein
  simp_rw [summand_unipotent]
  exact (cuspUnipotentEquiv t).tsum_eq _

theorem hyperbolicEisenstein_unipotent (t : ℤ) (s : ℂ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (integralComplexMatrix (rationalEmbedding (rationalUnipotent t)) • w)=
      hyperbolicEisenstein s w := by
  induction w using Quotient.inductionOn with
  | _ g => exact eisenstein_unipotent t g s

end CubicEisenstein

end

end OAI

end



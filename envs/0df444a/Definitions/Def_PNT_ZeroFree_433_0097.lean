-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0097
-- name    : PNT_ZeroFree_433_0097
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:32:57.17842+00:00
-- url     : https://prove2.me/theorems/b90c6540-0cd9-4c08-bfb5-484741fd89c1
-- title:
--   Zero-free region foundations: Eisenstein.ConstantDirichletSeries [0097]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.ConstantDirichletSeries
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ConstantDirichletSeries.lean#L79-L626

import Definitions.Def_PNT_ZeroFree_433_0096

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ConstantDirichletSeries.lean#L79-L626
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Eisenstein.ConstantDirichletSeries
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
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)

lemma constant_dirichlet_support (s : ℂ) :
    Function.support (arithmeticDirichletTerm s 0) ⊆
      {c : LevelLower | c.1 ≠ 0 ∧ ∃ a : O,c.1=a^3} := by
  intro c hc
  change arithmeticDirichletTerm s 0 c ≠ 0 at hc
  by_cases hzero : c.1=0
  · simp [arithmeticDirichletTerm,hzero] at hc
  · refine ⟨hzero, ?_⟩
    have hA : arithmeticResidueSum 0 c.1 ≠ 0 := by
      intro hA
      apply hc
      simp only [arithmeticDirichletTerm,if_neg hzero,hA,mul_zero]
    exact (arithmeticResidueSum_ne_zero_iff_cube c.1 hzero c.2).mp hA

lemma totient_sum_good (s : ℂ) :
    (∑' I : GoodIdeal,(idealTotient I.1:ℂ)*unramifiedNormWeight s I.1)=unramifiedTotientSeries s := by
  unfold unramifiedTotientSeries
  apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | primaryGenerator I ≠ 0})
    (f := fun I : Ideal O => (idealTotient I:ℂ)*unramifiedNormWeight s I)
  intro I hI
  change (idealTotient I:ℂ)*unramifiedNormWeight s I ≠ 0 at hI
  change primaryGenerator I ≠ 0
  intro hg
  apply hI
  rw [unramifiedNormWeight_of_bad _ I hg,mul_zero]

lemma norm_ramifiedRatio_lt_one (s : ℂ) (hs : 1<s.re) : ‖ramifiedRatio s‖<1 := by
  change ‖((3:ℝ):ℂ)^(3-3*s)‖<1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<3)]
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  norm_num
  linarith

theorem constantDirichlet_summable_norm (s : ℂ) (hs : (4:ℝ)/3<s.re) :
    Summable (fun c : LevelLower => ‖arithmeticDirichletTerm s 0 c‖) := by
  have hs1 : 1<s.re := by linarith
  have hw : 2<(3*s-2).re := by norm_num; linarith
  have hq := norm_ramifiedRatio_lt_one s hs1
  have hqn : Summable (fun n : ℕ => ‖ramifiedRatio s^(n+1)‖) := by
    have hh := (summable_geometric_of_lt_one (norm_nonneg (ramifiedRatio s)) hq).mul_right
      ‖ramifiedRatio s‖
    simpa only [pow_succ,norm_mul,norm_pow] using hh
  have hi := (unramifiedTotientSeries_summable_norm (3*s-2) hw).subtype
    (fun I : Ideal O => primaryGenerator I ≠ 0)
  have hni := hqn.mul_norm hi
  have hb : Summable (fun _ : Bool => ‖(1:ℂ)‖) := summable_of_hasFiniteSupport (Set.toFinite _)
  have hfull := hb.mul_norm hni
  have hp : Summable (fun p : Bool × ℕ × GoodIdeal =>
      ‖arithmeticDirichletTerm s 0 (cubeColumnMap p).1‖) := by
    apply hfull.congr
    rintro ⟨b,n,I⟩
    simp only [one_mul,cubeColumn_dirichletTerm]
  have hsub : Summable (fun c : CubeLower => ‖arithmeticDirichletTerm s 0 c.1‖) :=
    cubeColumnEquiv.summable_iff.mp hp
  have hind := (summable_subtype_iff_indicator
    (s := {c : LevelLower | c.1 ≠ 0 ∧ ∃ a : O,c.1=a^3})
    (f := fun c => ‖arithmeticDirichletTerm s 0 c‖)).mp hsub
  apply hind.congr
  intro c
  by_cases hc : c.1 ≠ 0 ∧ ∃ a : O,c.1=a^3
  · simp [Set.indicator,hc]
  · have hz : arithmeticDirichletTerm s 0 c=0 := by
      by_contra h
      exact hc (constant_dirichlet_support s h)
    simp [Set.indicator,hc,hz]

lemma ramified_geometric_sum (s : ℂ) (hs : 1<s.re) :
    (∑' n : ℕ,ramifiedRatio s^(n+1))=((3:ℂ)^(3*s-3)-1)⁻¹ := by
  have hn := norm_ramifiedRatio_lt_one s hs
  have hne : ramifiedRatio s ≠ 0 := by
    unfold ramifiedRatio
    apply Complex.cpow_ne_zero_iff.mpr
    exact Or.inl (by norm_num)
  have hone : ramifiedRatio s ≠ 1 := by intro h; rw [h,norm_one] at hn; exact lt_irrefl 1 hn
  have hi : (3:ℂ)^(3*s-3)=(ramifiedRatio s)⁻¹ := by
    rw [ramifiedRatio,← Complex.cpow_neg]
    congr 1
    ring
  simp_rw [pow_succ]
  rw [tsum_mul_right,tsum_geometric_of_norm_lt_one hn,hi]
  field_simp

theorem arithmeticDirichletSeries_zero_totient (s : ℂ) (hs : (4:ℝ)/3<s.re) :
    arithmeticDirichletSeries s 0 =
      2*((3:ℂ)^(3*s-3)-1)⁻¹*unramifiedTotientSeries (3*s-2) := by
  have hc := (constantDirichlet_summable_norm s hs).of_norm
  have hsub : Summable (fun c : CubeLower => arithmeticDirichletTerm s 0 c.1) := hc.subtype _
  have hp := cubeColumnEquiv.summable_iff.mpr hsub
  change Summable (fun p : Bool × ℕ × GoodIdeal =>
    arithmeticDirichletTerm s 0 (cubeColumnMap p).1) at hp
  calc
    _ = ∑' c : CubeLower,arithmeticDirichletTerm s 0 c.1 :=
      (tsum_subtype_eq_of_support_subset (constant_dirichlet_support s)).symm
    _ = ∑' p : Bool × ℕ × GoodIdeal,arithmeticDirichletTerm s 0 (cubeColumnMap p).1 :=
      (cubeColumnEquiv.tsum_eq _).symm
    _ = ∑' b : Bool,∑' n : ℕ,∑' I : GoodIdeal,
        arithmeticDirichletTerm s 0 (cubeColumnMap (b,n,I)).1 := by
      rw [hp.tsum_prod]
      apply tsum_congr
      intro b
      exact (hp.prod_factor b).tsum_prod
    _ = ∑' b : Bool,∑' n : ℕ,∑' I : GoodIdeal,
        ramifiedRatio s^(n+1)*((idealTotient I.1:ℂ)*unramifiedNormWeight (3*s-2) I.1) := by
      apply tsum_congr; intro b
      apply tsum_congr; intro n
      exact tsum_congr (fun I => cubeColumn_dirichletTerm s b n I)
    _ = ∑' _ : Bool,∑' n : ℕ,ramifiedRatio s^(n+1)*unramifiedTotientSeries (3*s-2) := by
      apply tsum_congr; intro b
      apply tsum_congr; intro n
      rw [tsum_mul_left,totient_sum_good]
    _ = ∑' _ : Bool,((3:ℂ)^(3*s-3)-1)⁻¹*unramifiedTotientSeries (3*s-2) := by
      apply tsum_congr; intro b
      rw [tsum_mul_right,ramified_geometric_sum s (by linarith)]
    _ = _ := by
      rw [tsum_fintype]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_bool,nsmul_eq_mul]
      ring

theorem scatteringCoefficient_zero_zeta (s : ℂ) (hs : (4:ℝ)/3<s.re) :
    scatteringCoefficient s 0 =
      (2/((9*Real.sqrt 3/2:ℝ):ℂ))*
      ((3:ℂ)^(3*s-3)-1)⁻¹ *
      (unramifiedIdealZeta (3*s-3)/unramifiedIdealZeta (3*s-2)) := by
  rw [scatteringCoefficient,arithmeticDirichletSeries_zero_totient s hs,
    unramifiedTotientSeries_quotient (3*s-2) (by
      norm_num
      linarith)]
  rw [show 3*s-2-1=3*s-3 by ring]
  ring

theorem eisensteinConstantCoefficient_zeta (v : ℝ) (hv : 0<v) (s : ℂ) (hs : 2<s.re) :
    eisensteinFourierCoefficient v hv s 0 = (v:ℂ)^s+
      (v:ℂ)^(2-s)*((Real.pi:ℂ)/(s-1))*
      ((2/((9*Real.sqrt 3/2:ℝ):ℂ))*((3:ℂ)^(3*s-3)-1)⁻¹*
        (unramifiedIdealZeta (3*s-3)/unramifiedIdealZeta (3*s-2))) := by
  rw [eisensteinConstantCoefficient_formula v hv s hs,scatteringCoefficient_zero_zeta s (by linarith)]

end CubicEisenstein

namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

theorem matrix_eq_primePool (M N : ℝ) (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I)
    (hM : idealRange M ⊆ F) (hN : idealRange N ⊆ F) :
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    matrix M N = QuadraticInitialBound.quadraticMatrix (poolPrimary F)
      (poolPrimary_good F hF)
      (fun I : idealRange M => idealSupport F I.val)
      (fun J : idealRange N => idealSupport F J.val) := by
  ext I J
  change quadraticRow J.val (primaryGenerator I.val) = _
  rw [quadraticRow_eq_primaryPool F hF J.val (hN J.property)]
  rw [primaryGenerator_eq_poolProduct F hF I.val (hM I.property)]
  rfl

theorem sieveNorm_reverse_le (M N : ℝ) :
    sieveNorm M N ≤ 262144 * sieveNorm N M := by
  let F := idealRange M ∪ idealRange N
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    rcases Finset.mem_union.mp hI with hI | hI
    · exact (mem_idealRange.mp hI).1
    · exact (mem_idealRange.mp hI).1
  have hM : idealRange M ⊆ F := Finset.subset_union_left
  have hN : idealRange N ⊆ F := Finset.subset_union_right
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have h := QuadraticInitialBound.quadraticSieveNorm_reverse_le
    (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) (poolPrimary_odd F hF)
    (fun I : idealRange M => idealSupport F I.val)
    (fun J : idealRange N => idealSupport F J.val)
  simpa only [QuadraticInitialBound.quadraticSieveNorm,
    ← matrix_eq_primePool M N F hF hM hN,
    ← matrix_eq_primePool N M F hF hN hM, sieveNorm] using h

end
section

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex
open TruncatedPrincipalPoisson QuadraticSquarefreeKernel

def dualPrincipalIdeal (I J : Ideal O) (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' A : NonzeroIdeal,
    (idealZeroMask I (idealGenerator A.val) * idealZeroMask J (idealGenerator A.val)) *
      V ((Ideal.absNorm A.val : ℝ) / X)

def dualPrincipalLattice (I J : Ideal O) (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' z : O, rowCoprimeMask (fun P : primePool {I * J} => P.val) Finset.univ z *
    V (‖eisEmbedding z‖ ^ 2 / X)

theorem idealZeroMask_pair_zero (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hnt : I ≠ 1 ∨ J ≠ 1) : idealZeroMask I 0 * idealZeroMask J 0 = 0 := by
  rw [← canonical_quadraticRow_squared I hI, ← canonical_quadraticRow_squared J hJ]
  calc
    _ = (quadraticRow I 0 * quadraticRow J 0) ^ 2 := by ring
    _ = 0 := by rw [quadratic_pair_zero_of_nontrivial I J hI hJ hnt]; ring

theorem dualPrincipalIdeal_eq_lattice (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hnt : I ≠ 1 ∨ J ≠ 1) (V : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    dualPrincipalIdeal I J V X = (6 : ℂ)⁻¹ * dualPrincipalLattice I J V X := by
  let P := fun P : primePool {I * J} => P.val
  let f : O → ℂ := fun z => rowCoprimeMask P Finset.univ z * V (‖eisEmbedding z‖ ^ 2 / X)
  have hV : Summable (fun z : O => ‖V (‖eisEmbedding z‖ ^ 2 / X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest V X hX)
  have hf : Summable f := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _ hV
    intro z
    dsimp only [f]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (QuadraticUnitInvariance.rowCoprimeMask_norm_le_one P Finset.univ z)
  have hm (z : O) : rowCoprimeMask P Finset.univ z = idealZeroMask I z * idealZeroMask J z := by
    rw [singleton_rowCoprimeMask_eq_idealZeroMask, idealZeroMask_mul I J hI.1 hJ.1]
  have h0 : f 0 = 0 := by
    dsimp only [f]
    rw [hm, idealZeroMask_pair_zero I J hI hJ hnt, zero_mul]
  have hu (u : Oˣ) (z : O) : f (u.val * z) = f z := by
    dsimp only [f]
    rw [QuadraticUnitInvariance.rowCoprimeMask_unit_mul, norm_eisEmbedding_unit_mul]
  have he := tsum_unit_invariant_of_zero f hf h0 hu
  have hd : (∑' A : NonzeroIdeal, f (idealGenerator A.val)) = dualPrincipalIdeal I J V X := by
    apply tsum_congr
    intro A
    simp only [f, hm, idealGenerator_norm_sq]
  change dualPrincipalLattice I J V X = 6 * ∑' A : NonzeroIdeal, f (idealGenerator A.val) at he
  rw [hd] at he
  rw [he]
  ring

theorem dualPrincipalIdeal_truncated (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hnt : I ≠ 1 ∨ J ≠ 1) (V : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ) (hX : 0 < X) :
    dualPrincipalIdeal I J V X = (6 : ℂ)⁻¹ *
      (principalTruncation (fun P : primePool {I * J} => P.val) Finset.univ V X Z +
       middleTruncation (fun P : primePool {I * J} => P.val) Finset.univ V X Y Z lengthScale +
       truncationError (fun P : primePool {I * J} => P.val) Finset.univ V X Y Z lengthScale) := by
  rw [dualPrincipalIdeal_eq_lattice I J hI hJ hnt V X hX]
  congr 1
  unfold truncationError
  have he : dualPrincipalLattice I J V X =
      ∑' z : O, rowCoprimeMask (fun P : primePool {I * J} => P.val) Finset.univ z *
        (if z = 0 then 0 else V (‖eisEmbedding z‖ ^ 2 / X)) := by
    apply tsum_congr
    intro z
    by_cases hz : z = 0
    · subst z
      rw [singleton_rowCoprimeMask_eq_idealZeroMask, idealZeroMask_mul I J hI.1 hJ.1,
        idealZeroMask_pair_zero I J hI hJ hnt, zero_mul, zero_mul]
    · simp only [if_neg hz]
  rw [he]
  ring

theorem canonical_pair_ideal_fourier_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ))
    (t : ℝ) (ht : 0 < t) :
    Summable (fun lengthScale : NonzeroIdeal => unrestrictedPairCharacter I J lengthScale.val *
      paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))) := by
  have hi : Function.Injective (fun lengthScale : NonzeroIdeal => idealGenerator lengthScale.val) := by
    intro A B he
    apply Subtype.ext
    have hs := congrArg (fun z : O => Ideal.span {z}) he
    simpa only [span_idealGenerator] using hs
  have h := (canonical_pair_fourier_summable I J W t ht).comp_injective hi
  simpa only [Function.comp_def, idealGenerator_norm_sq, unrestrictedPairCharacter] using h

theorem canonical_nonprincipal_dual_principal
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (hnt : I ≠ 1 ∨ J ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    (∑' h : O, (quadraticRow I h * quadraticRow J h) *
      paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)) =
      (6 : ℂ) * ∑' B : {B : Ideal O // Squarefree B},
        unrestrictedPairCharacter I J B.val *
          dualPrincipalIdeal I J (quadraticTransformedSquareProfile W)
            (Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))) := by
  rw [canonical_nonprincipal_dual_squarefree I J hI hJ hray hnt W t ht]
  congr 1
  let F : (NonzeroIdeal × {B : Ideal O // Squarefree B}) → ℂ := fun p =>
    (idealZeroMask I (idealGenerator p.1.val) * idealZeroMask J (idealGenerator p.1.val)) *
    unrestrictedPairCharacter I J p.2.val * paperRadialFourier W
      (t * ((Ideal.absNorm p.1.val : ℝ) ^ 2 * (Ideal.absNorm p.2.val : ℝ)))
  have hf : Summable F := by
    have hs := decompositionEquiv.symm.summable_iff.mpr
      (canonical_pair_ideal_fourier_summable I J W t ht)
    apply hs.congr
    intro p
    change unrestrictedPairCharacter I J (p.1.val ^ 2 * p.2.val) *
      paperRadialFourier W (t * (Ideal.absNorm (p.1.val ^ 2 * p.2.val) : ℝ)) = F p
    rw [unrestrictedPairCharacter_mul I J hI hJ hray,
      unrestrictedPairCharacter_square I J hI hJ hray]
    simp only [F, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
  change (∑' p, F p) = _
  calc
    _ = ∑' p : ({B : Ideal O // Squarefree B} × NonzeroIdeal), F (p.2, p.1) :=
      (Equiv.prodComm _ _).tsum_eq (fun p => F (p.2, p.1))
    _ = ∑' B : {B : Ideal O // Squarefree B}, ∑' A : NonzeroIdeal, F (A, B) := hf.prod_symm.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro B
      rw [dualPrincipalIdeal, ← tsum_mul_left]
      apply tsum_congr
      intro A
      have hB : 0 < (Ideal.absNorm B.val : ℝ) := by
        exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => B.property.ne_zero (Ideal.absNorm_eq_zero_iff.mp h))
      have htb : 0 < t * (Ideal.absNorm B.val : ℝ) := mul_pos ht hB
      have harg : ((Ideal.absNorm A.val : ℝ) / Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))) ^ 2 =
          t * ((Ideal.absNorm A.val : ℝ) ^ 2 * (Ideal.absNorm B.val : ℝ)) := by
        rw [div_pow, Real.sq_sqrt (one_div_pos.mpr htb).le]
        field_simp

      simp only [F, quadraticTransformedSquareProfile_apply, harg]
      ring

end
section

open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open QuadraticMainOperatorBound IdealCoprimeSieveOperator DivisorBlockCauchy

def canonicalMainBoundary (H : Finset (Ideal O)) (G : Ideal O) (K N : ℝ)
    (a : idealRange N → ℂ) : ℂ :=
  ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
    (UniqueFactorizationMonoid.moebius E : ℂ) *
    (∑ B : H, mainWeight K B.val D E *
      (∑ J : idealRange N, ∑ lengthScale : idealRange N, if IsCoprime J.val lengthScale.val then
        star (quadraticRow J.val (primaryGenerator B.val) *
          (a J * quadraticRow J.val (primaryGenerator D * primaryGenerator E))) *
        (quadraticRow lengthScale.val (primaryGenerator B.val) *
          (a lengthScale * quadraticRow lengthScale.val (primaryGenerator D * primaryGenerator E))) else 0))

theorem canonicalMainBoundary_bound
    (ε : ℝ) (hε : 0 < ε) (K N : ℝ) (hK : 0 < K) (hN : 0 ≤ N)
    (H : Finset (Ideal O)) (hH : H ⊆ idealRange K) (G : Ideal O) (hG : G ≠ 0)
    (a : idealRange N → ℂ) :
    ‖canonicalMainBoundary H G K N a‖ ≤
      ((idealDivisors G).card : ℝ) ^ 2 *
        ((1 / Real.sqrt K) * sieveNorm K N * (supportConstant ε hε * N ^ ε) *
          ∑ J, ‖a J‖ ^ 2) := by
  let A : Matrix H (idealRange N) ℂ := fun B J => quadraticRow J.val (primaryGenerator B.val)
  let r : Ideal O → Ideal O → idealRange N → ℂ := fun D E J =>
    quadraticRow J.val (primaryGenerator D * primaryGenerator E)
  have he := main_difference_operator_bound ε hε K hK G hG
    (fun B : H => B.val) (fun J : idealRange N => J.val)
    (fun J => (mem_idealRange.mp J.property).1.1) N hN
    (fun J => (mem_idealRange.mp J.property).2) A a r
    (fun D E J => quadraticRow_norm_le_one J.val _)
  have hA : ‖FiniteSieveOperator.operator A‖ ^ 2 ≤ sieveNorm K N :=
    family_squared_norm_le (fun B : H => B.val) (fun J : idealRange N => J.val)
      Subtype.val_injective Subtype.val_injective K N
      (fun B => mem_idealRange.mp (hH B.property)) (fun J => mem_idealRange.mp J.property)
  change ‖canonicalMainBoundary H G K N a‖ ≤ _ at he
  apply he.trans
  have hs : 0 ≤ supportConstant ε hε := (supportConstant_pos ε hε).le
  gcongr

theorem canonicalMainBoundary_small_power
    (ε : ℝ) (hε : 0 < ε) (K N : ℝ) (hK : 0 < K) (hN : 0 ≤ N)
    (H : Finset (Ideal O)) (hH : H ⊆ idealRange K) (G : Ideal O) (hG : G ≠ 0)
    (a : idealRange N → ℂ) :
    ‖canonicalMainBoundary H G K N a‖ ≤
      (divisorConstant ε hε * (Ideal.absNorm G : ℝ) ^ ε) ^ 2 *
        ((1 / Real.sqrt K) * sieveNorm K N * (supportConstant ε hε * N ^ ε) *
          ∑ J, ‖a J‖ ^ 2) := by
  apply (canonicalMainBoundary_bound ε hε K N hK hN H hH G hG a).trans
  have hd : ((idealDivisors G).card : ℝ) ≤ divisorConstant ε hε * (Ideal.absNorm G : ℝ) ^ ε :=
    (IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2 G hG
  have hs : 0 ≤ supportConstant ε hε := (supportConstant_pos ε hε).le
  have hB := sieveNorm_nonneg K N
  gcongr

theorem canonicalMainBoundary_reverse
    (ε : ℝ) (hε : 0 < ε) (K N : ℝ) (hK : 0 < K) (hN : 0 ≤ N)
    (H : Finset (Ideal O)) (hH : H ⊆ idealRange K) (G : Ideal O) (hG : G ≠ 0)
    (a : idealRange N → ℂ) :
    ‖canonicalMainBoundary H G K N a‖ ≤
      ((idealDivisors G).card : ℝ) ^ 2 *
        ((262144 / Real.sqrt K) * sieveNorm N K * (supportConstant ε hε * N ^ ε) *
          ∑ J, ‖a J‖ ^ 2) := by
  apply (canonicalMainBoundary_bound ε hε K N hK hN H hH G hG a).trans
  have hs : 0 ≤ supportConstant ε hε := (supportConstant_pos ε hε).le
  calc
    _ ≤ ((idealDivisors G).card : ℝ) ^ 2 *
        ((1 / Real.sqrt K) * (262144 * sieveNorm N K) * (supportConstant ε hε * N ^ ε) *
          ∑ J, ‖a J‖ ^ 2) := by gcongr; exact sieveNorm_reverse_le K N
    _ = _ := by ring

end

open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction

def CoefficientOnShell (N X : ℝ) (a : idealRange N → ℂ) : Prop :=
  ∀ J, a J ≠ 0 → X / 2 < (Ideal.absNorm J.val : ℝ) ∧ (Ideal.absNorm J.val : ℝ) ≤ X

theorem column_dyadic_exists (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale) (J : idealRange N) :
    ∃ j ∈ Finset.range (lengthScale + 1), (2 : ℝ) ^ j / 2 < (Ideal.absNorm J.val : ℝ) ∧
      (Ideal.absNorm J.val : ℝ) ≤ (2 : ℝ) ^ j := by
  have hn : 1 ≤ Ideal.absNorm J.val := Nat.one_le_iff_ne_zero.mpr
    (fun hz => (mem_idealRange.mp J.property).1.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  exact exists_dyadic_shell (Ideal.absNorm J.val) lengthScale hn ((mem_idealRange.mp J.property).2.trans hNL)

def columnDyadicSector (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale) (J : idealRange N) : Fin (lengthScale + 1) :=
  ⟨(column_dyadic_exists N lengthScale hNL J).choose,
    Finset.mem_range.mp (column_dyadic_exists N lengthScale hNL J).choose_spec.1⟩

def dyadicColumnCoefficient (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (j : Fin (lengthScale + 1)) (a : idealRange N → ℂ) : idealRange N → ℂ :=
  sectorCoefficient (columnDyadicSector N lengthScale hNL) j a

theorem dyadicColumnCoefficient_shell (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (j : Fin (lengthScale + 1)) (a : idealRange N → ℂ) :
    CoefficientOnShell N ((2 : ℝ) ^ j.val) (dyadicColumnCoefficient N lengthScale hNL j a) := by
  intro J hJ
  have he : columnDyadicSector N lengthScale hNL J = j := by
    by_contra hn
    exact hJ (by simp only [dyadicColumnCoefficient, sectorCoefficient, if_neg hn])
  have hs := (column_dyadic_exists N lengthScale hNL J).choose_spec.2
  have hv : (columnDyadicSector N lengthScale hNL J).val = j.val := congrArg Fin.val he
  change (column_dyadic_exists N lengthScale hNL J).choose = j.val at hv
  simpa only [hv] using hs

theorem dyadicColumnCoefficient_energy (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (a : idealRange N → ℂ) :
    (∑ j : Fin (lengthScale + 1), ∑ J, ‖dyadicColumnCoefficient N lengthScale hNL j a J‖ ^ 2) = ∑ J, ‖a J‖ ^ 2 :=
  sectorCoefficient_energy (columnDyadicSector N lengthScale hNL) a

theorem weighted_energy_column_shells {m : Type*} [Fintype m]
    (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (A : Matrix m (idealRange N) ℂ) (v : m → ℝ) (hv : ∀ i, 0 ≤ v i)
    (a : idealRange N → ℂ) :
    (∑ i, v i * ‖∑ J, A i J * a J‖ ^ 2) ≤
      (lengthScale + 1 : ℝ) * ∑ j : Fin (lengthScale + 1), ∑ i,
        v i * ‖∑ J, A i J * dyadicColumnCoefficient N lengthScale hNL j a J‖ ^ 2 := by
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, dyadicColumnCoefficient] using
    sector_weighted_energy_bound A (columnDyadicSector N lengthScale hNL) a v hv

theorem annularHighEnergy_column_shells (M N K : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (a : idealRange N → ℂ) :
    annularHighEnergy M N K a ≤ (lengthScale + 1 : ℝ) *
      ∑ j : Fin (lengthScale + 1), annularHighEnergy M N K (dyadicColumnCoefficient N lengthScale hNL j a) := by
  exact weighted_energy_column_shells N lengthScale hNL
    (fun I : highKernelRange (2 * M) K => fun J => quadraticRow J.val (primaryGenerator I.val))
    (fun I => annularHighWeight M I.val) (fun _ => QuadraticInitialBound.annularSieveBump.nonneg) a

def coefficientAtScale (N X : ℝ) (a : idealRange N → ℂ) (J : idealRange X) : ℂ :=
  if h : J.val ∈ idealRange N then a ⟨J.val, h⟩ else 0

theorem coefficientAtScale_shell (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : CoefficientOnShell X X (coefficientAtScale N X a) := by
  intro J hJ
  unfold coefficientAtScale at hJ
  split_ifs at hJ with h
  · exact ha ⟨J.val, h⟩ hJ
  · exact (hJ rfl).elim

theorem coefficientAtScale_row_sum (N X : ℝ) (a : idealRange N → ℂ)
    (ha : ∀ J, a J ≠ 0 → (Ideal.absNorm J.val : ℝ) ≤ X) (z : O) :
    (∑ J : idealRange N, quadraticRow J.val z * a J) =
      ∑ J : idealRange X, quadraticRow J.val z * coefficientAtScale N X a J := by
  let f : Ideal O → ℂ := fun I => if h : I ∈ idealRange N then quadraticRow I z * a ⟨I, h⟩ else 0
  have hleft : (∑ J : idealRange N, quadraticRow J.val z * a J) = ∑ I ∈ idealRange N, f I := by
    rw [← Finset.sum_coe_sort (idealRange N) f]
    apply Finset.sum_congr rfl
    intro J _
    simp only [f, dif_pos J.property]
  have hright : (∑ J : idealRange X, quadraticRow J.val z * coefficientAtScale N X a J) =
      ∑ I ∈ idealRange X, f I := by
    rw [← Finset.sum_coe_sort (idealRange X) f]
    apply Finset.sum_congr rfl
    intro J _
    unfold coefficientAtScale
    split_ifs with h <;> simp only [f, h, ↓reduceDIte, mul_zero]
  rw [hleft, hright]
  rcases le_total N X with hNX | hXN
  · apply Finset.sum_subset (idealRange_mono hNX)
    intro I hIX hIN
    simp only [f, dif_neg hIN]
  · symm
    apply Finset.sum_subset (idealRange_mono hXN)
    intro I hIN hIX
    have haI : a ⟨I, hIN⟩ = 0 := by
      by_contra hn
      exact hIX (mem_idealRange.mpr ⟨(mem_idealRange.mp hIN).1, ha ⟨I, hIN⟩ hn⟩)
    simp only [f, dif_pos hIN, haI, mul_zero]

theorem coefficientAtScale_energy (N X : ℝ) (a : idealRange N → ℂ)
    (ha : ∀ J, a J ≠ 0 → (Ideal.absNorm J.val : ℝ) ≤ X) :
    (∑ J : idealRange N, ‖a J‖ ^ 2) = ∑ J : idealRange X, ‖coefficientAtScale N X a J‖ ^ 2 := by
  let f : Ideal O → ℝ := fun I => if h : I ∈ idealRange N then ‖a ⟨I, h⟩‖ ^ 2 else 0
  have hleft : (∑ J : idealRange N, ‖a J‖ ^ 2) = ∑ I ∈ idealRange N, f I := by
    rw [← Finset.sum_coe_sort (idealRange N) f]
    apply Finset.sum_congr rfl
    intro J _
    simp only [f, dif_pos J.property]
  have hright : (∑ J : idealRange X, ‖coefficientAtScale N X a J‖ ^ 2) =
      ∑ I ∈ idealRange X, f I := by
    rw [← Finset.sum_coe_sort (idealRange X) f]
    apply Finset.sum_congr rfl
    intro J _
    unfold coefficientAtScale
    split_ifs with h <;> simp only [f, h, ↓reduceDIte, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  rw [hleft, hright]
  rcases le_total N X with hNX | hXN
  · apply Finset.sum_subset (idealRange_mono hNX)
    intro I hIX hIN
    simp only [f, dif_neg hIN]
  · symm
    apply Finset.sum_subset (idealRange_mono hXN)
    intro I hIN hIX
    have haI : a ⟨I, hIN⟩ = 0 := by
      by_contra hn
      exact hIX (mem_idealRange.mpr ⟨(mem_idealRange.mp hIN).1, ha ⟨I, hIN⟩ hn⟩)
    simp only [f, dif_pos hIN, haI, norm_zero, zero_pow (by decide : 2 ≠ 0)]

theorem annularHighEnergy_coefficientAtScale (M N X K : ℝ) (a : idealRange N → ℂ)
    (ha : ∀ J, a J ≠ 0 → (Ideal.absNorm J.val : ℝ) ≤ X) :
    annularHighEnergy M N K a = annularHighEnergy M X K (coefficientAtScale N X a) := by
  unfold annularHighEnergy
  simp_rw [coefficientAtScale_row_sum N X a ha]

theorem annularHighEnergy_column_shells_at_scale (M N K : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (a : idealRange N → ℂ) :
    annularHighEnergy M N K a ≤ (lengthScale + 1 : ℝ) * ∑ j : Fin (lengthScale + 1),
      annularHighEnergy M ((2 : ℝ) ^ j.val) K
        (coefficientAtScale N ((2 : ℝ) ^ j.val) (dyadicColumnCoefficient N lengthScale hNL j a)) := by
  apply (annularHighEnergy_column_shells M N K lengthScale hNL a).trans_eq
  apply congrArg (fun x : ℝ => (lengthScale + 1 : ℝ) * x)
  apply Finset.sum_congr rfl
  intro j _
  exact annularHighEnergy_coefficientAtScale M N _ K _
    (fun J hJ => (dyadicColumnCoefficient_shell N lengthScale hNL j a J hJ).2)

theorem dyadicColumnCoefficient_at_scale_energy (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (a : idealRange N → ℂ) :
    (∑ j : Fin (lengthScale + 1), ∑ J : idealRange ((2 : ℝ) ^ j.val),
      ‖coefficientAtScale N ((2 : ℝ) ^ j.val) (dyadicColumnCoefficient N lengthScale hNL j a) J‖ ^ 2) =
        ∑ J : idealRange N, ‖a J‖ ^ 2 := by
  calc
    _ = ∑ j : Fin (lengthScale + 1), ∑ J : idealRange N, ‖dyadicColumnCoefficient N lengthScale hNL j a J‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact (coefficientAtScale_energy N _ _
        (fun J hJ => (dyadicColumnCoefficient_shell N lengthScale hNL j a J hJ).2)).symm
    _ = _ := dyadicColumnCoefficient_energy N lengthScale hNL a

end CanonicalQuadraticSieve

end

end OAI

end



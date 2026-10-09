-- Prove2me | Definitions.Def_OAIHecke78B007
-- name    : OAIHecke78B007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T22:22:47.85719+00:00
-- url     : https://prove2.me/theorems/678e8ee8-9e8d-424d-bd42-924dcb03bdc4
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 8 of 29
-- statement:
--   Definitions bundle 8 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B006` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `Eisenstein.ConstantDirichletSeries`, `QuadraticSieve.DyadicColumns`, `CubicSieve.FirstCoreCutoff`, `QuadraticSieve.PrincipalDifference`, `QuadraticSieve.SpatialDerivatives`, `Eisenstein.SmoothSummands`, `Poisson.LatticeEnvelopes`, `QuadraticSieve.GreenIntegrals`, `CubicSieve.LogarithmicTargets`, `Eisenstein.SmoothCuspCutoffs`, `Eisenstein.SeedDefects`, `QuadraticSieve.PrincipalMajorants`, `QuadraticSieve.RetainedDualBounds`, `QuadraticSieve.HighKernelGeometry`, `Eisenstein.QuotientTopology`, `CubicSieve.PrincipalDensity`, `QuadraticSieve.CommonMasks`, `QuadraticSieve.PoissonComparison`, `CubicSieve.ArithmeticBins`, `Eisenstein.HyperbolicVolume`, `QuadraticSieve.GlobalBinLoss`, `QuadraticSieve.PoissonConstants`, `GaussSum.PowerfulParts`, `MeanSquare.SourceTransfer`, `CubicSieve.DensityBudgets`, `Eisenstein.SourceMellinInversion`, `GaussSum.BesselReflection`, `GaussSum.DualKernelSummability`, `CubicSieve.FullExtraction`, `CubicSieve.Dyadic`, `CubicSieve.ColumnShells`, `Descent.ChildCutoff`, `Descent.CompletedReopening`, `Descent.Dyadic`, `Descent.FirstRetainedFamily`, `Descent.FirstGlobalPush`, `Detector.RowAnalytic`, `Detector.GramFiniteGcd`, `Hecke.ReciprocalBound`, `PrimeRows.RowCount`, `Reflection.RawTail`, `Reflection.DyadicTail`, `Reflection.DyadicBox`, `Reflection.TruncatedSource`, `Reflection.TupleDyads`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B006

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B007

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  Eisenstein.ConstantDirichletSeries
  QuadraticSieve.DyadicColumns
  CubicSieve.FirstCoreCutoff
  QuadraticSieve.PrincipalDifference
  QuadraticSieve.SpatialDerivatives
  Eisenstein.SmoothSummands
  Poisson.LatticeEnvelopes
  QuadraticSieve.GreenIntegrals
  CubicSieve.LogarithmicTargets
  Eisenstein.SmoothCuspCutoffs
  Eisenstein.SeedDefects
  QuadraticSieve.PrincipalMajorants
  QuadraticSieve.RetainedDualBounds
  QuadraticSieve.HighKernelGeometry
  Eisenstein.QuotientTopology
  CubicSieve.PrincipalDensity
  QuadraticSieve.CommonMasks
  QuadraticSieve.PoissonComparison
  CubicSieve.ArithmeticBins
  Eisenstein.HyperbolicVolume
  QuadraticSieve.GlobalBinLoss
  QuadraticSieve.PoissonConstants
  GaussSum.PowerfulParts
  MeanSquare.SourceTransfer
  CubicSieve.DensityBudgets
  Eisenstein.SourceMellinInversion
  GaussSum.BesselReflection
  GaussSum.DualKernelSummability
  CubicSieve.FullExtraction
  CubicSieve.Dyadic
  CubicSieve.ColumnShells
  Descent.ChildCutoff
  Descent.CompletedReopening
  Descent.Dyadic
  Descent.FirstRetainedFamily
  Descent.FirstGlobalPush
  Detector.RowAnalytic
  Detector.GramFiniteGcd
  Hecke.ReciprocalBound
  PrimeRows.RowCount
  Reflection.RawTail
  Reflection.DyadicTail
  Reflection.DyadicBox
  Reflection.TruncatedSource
  Reflection.TupleDyads
-/

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

def coefficientAtScale (N X : ℝ) (a : idealRange N → ℂ) (J : idealRange X) : ℂ :=
  if h : J.val ∈ idealRange N then a ⟨J.val, h⟩ else 0

end CanonicalQuadraticSieve

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
namespace CanonicalQuadraticSieve

def columnDyadicLength (N : ℝ) : ℕ := ⌈Real.log N / Real.log 2⌉₊

theorem columnDyadicLength_cover (N : ℝ) : N ≤ (2 : ℝ) ^ columnDyadicLength N := by
  apply Real.pow_le_of_le_log (by norm_num : (0 : ℝ) < 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (div_le_iff₀ hlog).mp (Nat.le_ceil (Real.log N / Real.log 2))

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex QuadraticSquarefreeKernel

def dualSquarefreeTail (I J : Ideal O) (W : ℝ → ℂ) (t K : ℝ) : ℂ :=
  ∑' lengthScale : {lengthScale : Ideal O // lengthScale ≠ 0 ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)},
    unrestrictedPairCharacter I J lengthScale.val * paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))

end CanonicalQuadraticSieve

open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)

def fullIdealWeight (s : ℂ) (I : Ideal O) : ℂ :=
  if I=0 then 0 else (Ideal.absNorm I:ℂ)^(-s)

lemma norm_fullIdealWeight (s : ℂ) (I : NonzeroIdeal) :
    ‖fullIdealWeight s I.1‖=‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator I.1)‖^(-2*s.re) := by
  rw [fullIdealWeight,if_neg I.2]
  have hn : 0<‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator I.1)‖ :=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (ConcretePrimeRowBridge.idealGenerator_ne_zero _ I.2))
  have hnorm : ‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator I.1)‖^2=(Ideal.absNorm I.1:ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ConcretePrimeRowBridge.span_idealGenerator]
  have hcast : (Ideal.absNorm I.1:ℂ)=((‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator I.1)‖^2:ℝ):ℂ) := by
    exact_mod_cast hnorm.symm
  rw [hcast,Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hn),← Real.rpow_natCast_mul hn.le 2]
  congr 1
  simp only [Complex.neg_re,Nat.cast_ofNat]
  ring

theorem fullIdealWeight_summable_norm (s : ℂ) (hs : 1<s.re) :
    Summable (fun I : Ideal O => ‖fullIdealWeight s I‖) := by
  have hinj : Function.Injective (fun I : NonzeroIdeal => ConcretePrimeRowBridge.idealGenerator I.1) :=
    ConcretePrimeRowBridge.idealGenerator_injective.comp Subtype.val_injective
  have hlat := (summable_embedding_rpow (-2*s.re) (by linarith)).comp_injective hinj
  have hsub : Summable (fun I : NonzeroIdeal => ‖fullIdealWeight s I.1‖) := by
    simpa only [Function.comp_def,norm_fullIdealWeight] using hlat
  have hind := (summable_subtype_iff_indicator (s := {I : Ideal O | I ≠ 0})
    (f := fun I => ‖fullIdealWeight s I‖)).mp hsub
  apply hind.congr
  intro I
  by_cases hI : I=0
  · subst I
    simp [Set.indicator,fullIdealWeight]
  · have hIbot : I ≠ ⊥ := hI
    simp [Set.indicator,hIbot,fullIdealWeight]

def fullIdealZeta (s : ℂ) : ℂ := ∑' I : Ideal O,fullIdealWeight s I

lemma fullIdealWeight_norm_fiber (s : ℂ) (n : ℕ) :
    (∑' I : {I : Ideal O // Ideal.absNorm I=n},fullIdealWeight s I.1)=
      LSeries.term (fun n => (Nat.card {I : Ideal O // Ideal.absNorm I=n}:ℂ)) s n := by
  by_cases hn : n=0
  · subst n
    have hzero (I : {I : Ideal O // Ideal.absNorm I=0}) : fullIdealWeight s I.1=0 := by
      have hz : I.1=(0:Ideal O) := Ideal.absNorm_eq_zero_iff.mp I.2
      rw [fullIdealWeight,if_pos hz]
    simp only [hzero,tsum_zero,LSeries.term_zero]
  · let : Fintype {I : Ideal O // Ideal.absNorm I=n} :=
      (Ideal.finite_setOfPred_absNorm_eq (S := O) n).fintype
    have hterm (I : {I : Ideal O // Ideal.absNorm I=n}) : fullIdealWeight s I.1=(n:ℂ)^(-s) := by
      have hI : I.1 ≠ 0 := fun h => hn (by rw [← I.2,h,map_zero])
      rw [fullIdealWeight,if_neg hI,I.2]
    simp only [hterm,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      LSeries.term_of_ne_zero hn,Nat.card_eq_fintype_card,Complex.cpow_neg,div_eq_mul_inv]

theorem fullIdealZeta_eq_dedekindZeta (s : ℂ) (hs : 1<s.re) :
    fullIdealZeta s=NumberField.dedekindZeta ActualEisensteinCubic.K s := by
  have h := (fullIdealWeight_summable_norm s hs).of_norm.hasSum.tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ =>
    ∑' I : {I : Ideal O // Ideal.absNorm I=n},fullIdealWeight s I.1) (fullIdealZeta s) at h
  simp_rw [fullIdealWeight_norm_fiber] at h
  exact h.tsum_eq.symm

lemma fullIdealWeight_lambdaFactor (s : ℂ) (n : ℕ) (I : GoodIdeal) :
    fullIdealWeight s (lambdaFactorMap (n,I)).1=((3:ℂ)^(-s))^n*unramifiedNormWeight s I.1 := by
  rw [fullIdealWeight,if_neg (lambdaFactorMap (n,I)).2]
  change (Ideal.absNorm (ramifiedIdeal^n*I.1):ℂ)^(-s)=_
  rw [map_mul,map_pow,ramifiedIdeal_absNorm,Nat.cast_mul,
    unramifiedNormWeight_of_good _ _ I.2]
  rw [Complex.natCast_mul_natCast_cpow]
  congr 1
  have h := (Complex.natCast_cpow_natCast_mul 3 n (-s)).symm.trans (Complex.cpow_nat_mul 3 n (-s))
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using h

theorem unramifiedIdealZeta_eq_dedekindZeta (s : ℂ) (hs : 1<s.re) :
    unramifiedIdealZeta s=(1-(3:ℂ)^(-s))*NumberField.dedekindZeta ActualEisensteinCubic.K s := by
  have hnorm : ‖(3:ℂ)^(-s)‖<1 := by
    change ‖((3:ℝ):ℂ)^(-s)‖<1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<3)]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    simp only [Complex.neg_re]
    linarith
  have hne : 1-(3:ℂ)^(-s) ≠ 0 := by
    intro h
    have hz : (3:ℂ)^(-s)=1 := (sub_eq_zero.mp h).symm
    rw [hz,norm_one] at hnorm
    exact lt_irrefl 1 hnorm
  have hsub : Summable (fun I : NonzeroIdeal => fullIdealWeight s I.1) :=
    (fullIdealWeight_summable_norm s hs).of_norm.subtype _
  have hp := lambdaFactorEquiv.summable_iff.mpr hsub
  change Summable (fun p : ℕ × GoodIdeal => fullIdealWeight s (lambdaFactorMap p).1) at hp
  have hfull : fullIdealZeta s=(1-(3:ℂ)^(-s))⁻¹*unramifiedIdealZeta s := by
    calc
      _ = ∑' I : NonzeroIdeal,fullIdealWeight s I.1 := by
        symm
        apply tsum_subtype_eq_of_support_subset
        intro I hI
        change I ≠ 0
        intro hz
        exact hI (by simp [fullIdealWeight,hz])
      _ = ∑' p : ℕ × GoodIdeal,fullIdealWeight s (lambdaFactorMap p).1 :=
        (lambdaFactorEquiv.tsum_eq _).symm
      _ = ∑' n : ℕ,∑' I : GoodIdeal,((3:ℂ)^(-s))^n*unramifiedNormWeight s I.1 := by
        rw [hp.tsum_prod]
        apply tsum_congr; intro n
        exact tsum_congr (fun I => fullIdealWeight_lambdaFactor s n I)
      _ = ∑' n : ℕ,((3:ℂ)^(-s))^n*unramifiedIdealZeta s := by
        apply tsum_congr; intro n
        rw [tsum_mul_left]
        apply congrArg (fun z : ℂ => ((3:ℂ)^(-s))^n*z)
        apply tsum_subtype_eq_of_support_subset (f := unramifiedNormWeight s)
          (s := {I : Ideal O | primaryGenerator I ≠ 0})
        intro I hI
        change primaryGenerator I ≠ 0
        intro hz
        exact hI (unramifiedNormWeight_of_bad s I hz)
      _ = _ := by rw [tsum_mul_right,tsum_geometric_of_norm_lt_one hnorm]
  rw [← fullIdealZeta_eq_dedekindZeta s hs,hfull,← mul_assoc,mul_inv_cancel₀ hne,one_mul]

end
section

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss

lemma constantDirichletTerm_differentiable (c : LevelLower) :
    Differentiable ℂ (fun s : ℂ => arithmeticDirichletTerm s 0 c) := by
  by_cases hc : c.1=0
  · simp only [arithmeticDirichletTerm,if_pos hc]
    exact differentiable_const _
  · have hq : ((‖eisEmbedding c.1‖^2:ℝ):ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc)))
    simp only [arithmeticDirichletTerm,if_neg hc]
    exact (differentiable_id.neg.const_cpow (Or.inl hq)).mul_const _

lemma constantDirichletTerm_norm_mono (a : ℝ) (s : ℂ) (ha : a ≤ s.re) (c : LevelLower) :
    ‖arithmeticDirichletTerm s 0 c‖ ≤ ‖arithmeticDirichletTerm (a:ℂ) 0 c‖ := by
  by_cases hc : c.1=0
  · simp only [arithmeticDirichletTerm,if_pos hc,norm_zero,le_refl]
  · have hpos : 0<‖eisEmbedding c.1‖^2 := sq_pos_of_pos
      (norm_pos_iff.mpr (eisEmbedding_ne_zero hc))
    have hq : 1≤‖eisEmbedding c.1‖^2 := by
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
    simp only [arithmeticDirichletTerm,if_neg hc,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos,Complex.neg_re,Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg ha))
      (norm_nonneg _)

theorem arithmeticDirichletSeries_zero_differentiableAt (s : ℂ) (hs : (4:ℝ)/3<s.re) :
    DifferentiableAt ℂ (fun z => arithmeticDirichletSeries z 0) s := by
  let a : ℝ := ((4:ℝ)/3+s.re)/2
  have ha : (4:ℝ)/3<a := by dsimp [a]; linarith
  have has : a<s.re := by dsimp [a]; linarith
  have hsum := constantDirichlet_summable_norm (a:ℂ) (by simpa using ha)
  have hopen : IsOpen {z : ℂ | a<z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun z => arithmeticDirichletSeries z 0) {z : ℂ | a<z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun c => (constantDirichletTerm_differentiable c).differentiableOn) hopen
    intro c z hz
    exact constantDirichletTerm_norm_mono a z hz.le c
  exact (hd s has).differentiableAt (hopen.mem_nhds has)

lemma unramifiedNormWeight_differentiable (I : Ideal O) :
    Differentiable ℂ (fun s : ℂ => unramifiedNormWeight s I) := by
  by_cases hI : primaryGenerator I=0
  · simp only [unramifiedNormWeight_of_bad _ I hI]
    exact differentiable_const _
  · have hn : (Ideal.absNorm I:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (primaryGenerator_ne_zero_ideal I hI))
    simp only [unramifiedNormWeight_of_good _ I hI]
    exact differentiable_id.neg.const_cpow (Or.inl hn)

lemma unramifiedNormWeight_norm_mono (a : ℝ) (s : ℂ) (ha : a ≤ s.re) (I : Ideal O) :
    ‖unramifiedNormWeight s I‖≤‖unramifiedNormWeight (a:ℂ) I‖ := by
  by_cases hI : primaryGenerator I=0
  · simp only [unramifiedNormWeight_of_bad _ I hI,norm_zero,le_refl]
  · have hn : Ideal.absNorm I ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr (primaryGenerator_ne_zero_ideal I hI)
    have hpos : (0:ℝ)<Ideal.absNorm I := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hq : (1:ℝ)≤Ideal.absNorm I := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    simp only [unramifiedNormWeight_of_good _ I hI]
    change ‖((Ideal.absNorm I:ℝ):ℂ)^(-s)‖≤‖((Ideal.absNorm I:ℝ):ℂ)^(-(a:ℂ))‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos,Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    exact Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg ha)

theorem unramifiedIdealZeta_differentiableAt (s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ unramifiedIdealZeta s := by
  let a : ℝ := (1+s.re)/2
  have ha : 1<a := by dsimp [a]; linarith
  have has : a<s.re := by dsimp [a]; linarith
  have hsum := unramifiedNormWeight_summable_norm (a:ℂ) (by simpa using ha)
  have hopen : IsOpen {z : ℂ | a<z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ unramifiedIdealZeta {z : ℂ | a<z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun I => (unramifiedNormWeight_differentiable I).differentiableOn) hopen
    intro I z hz
    exact unramifiedNormWeight_norm_mono a z hz.le I
  exact (hd s has).differentiableAt (hopen.mem_nhds has)

end

open Filter
open scoped BigOperators Classical Topology

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss

def unramifiedZetaResidue : ℂ :=
  (2/3:ℂ)*(NumberField.dedekindZeta_residue ActualEisensteinCubic.K:ℂ)

lemma unramifiedZetaResidue_ne_zero : unramifiedZetaResidue ≠ 0 := by
  apply mul_ne_zero (by norm_num)
  exact Complex.ofReal_ne_zero.mpr
    (NumberField.dedekindZeta_residue_pos ActualEisensteinCubic.K).ne'

theorem unramifiedIdealZeta_oneSidedResidue :
    Tendsto (fun x : ℝ => ((x:ℂ)-1)*unramifiedIdealZeta (x:ℂ))
      (𝓝[>] (1:ℝ)) (𝓝 unramifiedZetaResidue) := by
  have hcont : Continuous (fun x : ℝ => 1-(3:ℂ)^(-(x:ℂ))) :=
    continuous_const.sub (Complex.continuous_ofReal.neg.const_cpow (Or.inl (by norm_num)))
  have heuler : Tendsto (fun x : ℝ => 1-(3:ℂ)^(-(x:ℂ))) (𝓝[>] (1:ℝ)) (𝓝 (2/3:ℂ)) := by
    apply (hcont.tendsto' 1 (2/3:ℂ) ?_).mono_left nhdsWithin_le_nhds
    norm_num [Complex.cpow_neg]
  have h := heuler.mul (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT ActualEisensteinCubic.K)
  change Tendsto (fun x : ℝ => (1-(3:ℂ)^(-(x:ℂ)))*
    (((x:ℂ)-1)*NumberField.dedekindZeta ActualEisensteinCubic.K (x:ℂ)))
      (𝓝[>] (1:ℝ)) (𝓝 unramifiedZetaResidue) at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 1<(x:ℂ).re := by simpa only [Set.mem_Ioi,Complex.ofReal_re] using hx
  rw [unramifiedIdealZeta_eq_dedekindZeta (x:ℂ) hx']
  ring

lemma cusp_volume_ne_zero : ((9*Real.sqrt 3/2:ℝ):ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  positivity

def constantArithmeticResidue : ℂ := unramifiedZetaResidue /
  (3*((9*Real.sqrt 3/2:ℝ):ℂ)*unramifiedIdealZeta 2)

lemma constantArithmeticResidue_ne_zero : constantArithmeticResidue ≠ 0 := by
  apply div_ne_zero unramifiedZetaResidue_ne_zero
  exact mul_ne_zero (mul_ne_zero (by norm_num) cusp_volume_ne_zero)
    (unramifiedIdealZeta_ne_zero 2 (by norm_num))

lemma tendsto_three_mul_sub_three_four_thirds :
    Tendsto (fun x : ℝ => 3*x-3) (𝓝[>] ((4:ℝ)/3)) (𝓝[>] (1:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · apply ((continuous_const.mul continuous_id).sub continuous_const).tendsto' _ _ (by norm_num)
      |>.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_Ioi] at hx ⊢
    linarith

theorem scatteringCoefficient_zero_oneSidedResidue :
    Tendsto (fun x : ℝ => ((x:ℂ)-(4/3:ℂ))*scatteringCoefficient (x:ℂ) 0)
      (𝓝[>] ((4:ℝ)/3)) (𝓝 constantArithmeticResidue) := by
  have hn0 := unramifiedIdealZeta_oneSidedResidue.comp tendsto_three_mul_sub_three_four_thirds
  have hn : Tendsto (fun x : ℝ => ((x:ℂ)-(4/3:ℂ))*unramifiedIdealZeta (3*(x:ℂ)-3))
      (𝓝[>] ((4:ℝ)/3)) (𝓝 (unramifiedZetaResidue/3)) := by
    convert (preTransparency := .instances) hn0.div_const (3:ℂ) using 1
    ext x
    dsimp only [Function.comp_def]
    push_cast
    ring
  have harg : Tendsto (fun x : ℝ => 3*(x:ℂ)-2) (𝓝[>] ((4:ℝ)/3)) (𝓝 (2:ℂ)) := by
    apply (((Complex.continuous_ofReal.const_mul 3).sub continuous_const).tendsto' _ _ ?_).mono_left
      nhdsWithin_le_nhds
    norm_num
  have hz := (unramifiedIdealZeta_differentiableAt 2 (by norm_num)).continuousAt.tendsto.comp harg
  have hdncont : Continuous (fun x : ℝ => (3:ℂ)^(3*(x:ℂ)-3)-1) :=
    (((Complex.continuous_ofReal.const_mul 3).sub continuous_const).const_cpow
      (Or.inl (by norm_num))).sub continuous_const
  have hdn : Tendsto (fun x : ℝ => (3:ℂ)^(3*(x:ℂ)-3)-1)
      (𝓝[>] ((4:ℝ)/3)) (𝓝 (2:ℂ)) := by
    apply (hdncont.tendsto' _ _ ?_).mono_left nhdsWithin_le_nhds
    norm_num
  have hp := ((hdn.inv₀ (by norm_num)).const_mul
    (2/((9*Real.sqrt 3/2:ℝ):ℂ))).mul
      (hn.div hz (unramifiedIdealZeta_ne_zero 2 (by norm_num)))
  have hlimit : (2/((9*Real.sqrt 3/2:ℝ):ℂ))*(2:ℂ)⁻¹*
      ((unramifiedZetaResidue/3)/unramifiedIdealZeta 2)=constantArithmeticResidue := by
    unfold constantArithmeticResidue
    ring
  rw [hlimit] at hp
  apply hp.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : (4:ℝ)/3<(x:ℂ).re := by simpa only [Set.mem_Ioi,Complex.ofReal_re] using hx
  rw [scatteringCoefficient_zero_zeta (x:ℂ) hx']
  dsimp only [Pi.div_apply,Function.comp_def]
  ring

end CubicEisenstein

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex QuadraticSquarefreeKernel

def dualSquarefreeLow (I J : Ideal O) (W : ℝ → ℂ) (t K : ℝ) : ℂ :=
  ∑' lengthScale : NonzeroIdeal, if (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) ≤ K then
    unrestrictedPairCharacter I J lengthScale.val * paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ)) else 0

end CanonicalQuadraticSieve

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

def HasSieveExponent (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    sieveNorm M N ≤ C * (M * N) ^ ε * (M + N ^ α)

theorem HasSieveExponent.reverse {α : ℝ} (h : HasSieveExponent α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      sieveNorm M N ≤ C * (M * N) ^ ε * (N + M ^ α) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h ε hε
  refine ⟨262144 * C, by positivity, ?_⟩
  intro M N hM hN
  calc
    _ ≤ 262144 * sieveNorm N M := sieveNorm_reverse_le M N
    _ ≤ 262144 * (C * (N * M) ^ ε * (N + M ^ α)) :=
      mul_le_mul_of_nonneg_left (hb N M hN hM) (by norm_num)
    _ = _ := by rw [mul_comm N M]; ring

theorem sqrt_divisor_sieve_pair_le (M N D₁ D₂ Q C : ℝ)
    (hN : 0 ≤ N) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (h₁ : sieveNorm M (N / D₁) ≤ C * (N / D₁ + Q))
    (h₂ : sieveNorm M (N / D₂) ≤ C * (N / D₂ + Q)) :
    Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) ≤
      C * (N + Q * (D₁ * D₂)) := by
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hD₁le : D₁ ≤ D₁ * D₂ := by nlinarith
  have hD₂le : D₂ ≤ D₁ * D₂ := by nlinarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ D₁ * D₂ * (C * (N / D₁ + Q)) * (C * (N / D₂ + Q)) := by
      gcongr
      exact sieveNorm_nonneg _ _
    _ = C ^ 2 * ((N + Q * D₁) * (N + Q * D₂)) := by field_simp
    _ ≤ C ^ 2 * ((N + Q * (D₁ * D₂)) * (N + Q * (D₁ * D₂))) := by gcongr
    _ = _ := by ring

theorem HasSieveExponent.divisor_pair {α : ℝ} (h : HasSieveExponent α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N D₁ D₂ : ℝ,
      1 ≤ M → 1 ≤ N → 1 ≤ D₁ → 1 ≤ D₂ → D₁ ≤ N → D₂ ≤ N →
      Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) ≤
        C * (M * N) ^ ε * (N + M ^ α * (D₁ * D₂)) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h.reverse ε hε
  refine ⟨C, hC, ?_⟩
  intro M N D₁ D₂ hM hN hD₁ hD₂ hD₁N hD₂N
  have hbound (D : ℝ) (hD : 1 ≤ D) (hDN : D ≤ N) :
      sieveNorm M (N / D) ≤ (C * (M * N) ^ ε) * (N / D + M ^ α) := by
    have hD0 : 0 < D := by linarith
    have hND : 1 ≤ N / D := (le_div_iff₀ hD0).mpr (by simpa using hDN)
    apply (hb M (N / D) hM hND).trans
    have hprod : M * (N / D) ≤ M * N := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact div_le_self (by linarith) hD
    gcongr
  exact sqrt_divisor_sieve_pair_le M N D₁ D₂ (M ^ α) (C * (M * N) ^ ε)
    (by linarith) hD₁ hD₂ (Real.rpow_nonneg (by linarith) _) (by positivity)
    (hbound D₁ hD₁ hD₁N) (hbound D₂ hD₂ hD₂N)

open IdealCoprimeSieveOperator DivisorBlockCauchy

variable {n p : Type*} [Fintype n] [Fintype p]

def divisorEnergyFactor (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a : n → ℂ) (b : p → ℂ) : ℝ :=
  256 * (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2 *
    Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ k, ‖b k‖ ^ 2)

end CanonicalQuadraticSieve

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum QuadraticMainBoundary QuadraticMainOperatorBound IdealCoprimeSieveOperator

def actualPrincipalDifference {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (G : Ideal O) (K : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j) * a k *
      (normalizedPairPartial (cols j) (cols k) K * normalizedPairDivisors (cols j) (cols k) G -
       normalizedPairCoprimePartial (cols j) (cols k) G K * normalizedPairDensity (cols j) (cols k) G)
    else 0

end

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def middleRatio (B b D₁ d D₂ e : ℝ) : ℝ := Real.sqrt (B / b) * (D₁ / d) * (D₂ / e)

theorem middleRatio_bounds (B b D₁ d D₂ e : ℝ)
    (hB : 0 < B) (hb : B / 2 ≤ b ∧ b ≤ B)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d ∧ d ≤ 2 * D₁)
    (hD₂ : 0 < D₂) (he : D₂ ≤ e ∧ e ≤ 2 * D₂) :
    1 / 4 ≤ middleRatio B b D₁ d D₂ e ∧ middleRatio B b D₁ d D₂ e ≤ 2 := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd.1
  have he0 : 0 < e := hD₂.trans_le he.1
  have hu1 : 1 ≤ Real.sqrt (B / b) := by
    have hq : 1 ≤ B / b := (le_div_iff₀ hb0).mpr (by simpa using hb.2)
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hq
  have hu2 : Real.sqrt (B / b) ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ hb0).mpr
    nlinarith
  have hv : (1 / 2 : ℝ) ≤ D₁ / d ∧ D₁ / d ≤ 1 :=
    ⟨(le_div_iff₀ hd0).mpr (by linarith), (div_le_one hd0).mpr hd.1⟩
  have hw : (1 / 2 : ℝ) ≤ D₂ / e ∧ D₂ / e ≤ 1 :=
    ⟨(le_div_iff₀ he0).mpr (by linarith), (div_le_one he0).mpr he.1⟩
  have hv0 : 0 ≤ D₁ / d := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hv.1
  have hw0 : 0 ≤ D₂ / e := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hw.1
  have hvw1 : (1 / 4 : ℝ) ≤ (D₁ / d) * (D₂ / e) := by
    nlinarith [mul_le_mul hv.1 hw.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) hv0]
  have hvw2 : (D₁ / d) * (D₂ / e) ≤ 1 := by
    nlinarith [mul_le_mul hv.2 hw.2 hw0 (by norm_num : (0 : ℝ) ≤ 1)]
  unfold middleRatio
  constructor
  · nlinarith [mul_le_mul hu1 hvw1 (by norm_num : (0 : ℝ) ≤ 1 / 4) (Real.sqrt_nonneg (B / b))]
  · nlinarith [mul_le_mul hu2 hvw2 (mul_nonneg hv0 hw0) (by norm_num : (0 : ℝ) ≤ 2)]

theorem middleRatio_log_bound (r : ℝ) (hr : (1 / 4 : ℝ) ≤ r ∧ r ≤ 2) : |Real.log r| ≤ 4 := by
  have hr0 : 0 < r := by linarith
  have hi : r⁻¹ ≤ 4 := by
    have h : (1 : ℝ) / r ≤ 4 := (div_le_iff₀ hr0).mpr (by linarith)
    simpa only [one_div] using h
  have h₁ := Real.log_le_sub_one_of_pos hr0
  have h₂ := Real.log_le_sub_one_of_pos (inv_pos.mpr hr0)
  rw [Real.log_inv] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem middleRatio_argument (M B b D₁ d D₂ e q : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b ∧ b ≤ B)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d ∧ d ≤ 2 * D₁)
    (hD₂ : 0 < D₂) (he : D₂ ≤ e ∧ e ≤ 2 * D₂) :
    (Real.sqrt (M / B) * q / (D₁ * D₂)) * Real.exp (Real.log (middleRatio B b D₁ d D₂ e)) =
      Real.sqrt (M / b) * q / (d * e) := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd.1
  have he0 : 0 < e := hD₂.trans_le he.1
  have hr : 0 < middleRatio B b D₁ d D₂ e := by
    have hh := middleRatio_bounds B b D₁ d D₂ e hB hb hD₁ hd hD₂ he
    linarith
  rw [Real.exp_log hr]
  have hs : Real.sqrt (M / B) * Real.sqrt (B / b) = Real.sqrt (M / b) := by
    rw [← Real.sqrt_mul (div_nonneg hM.le hB.le)]
    congr 1
    field_simp
  unfold middleRatio
  calc
    _ = (Real.sqrt (M / B) * Real.sqrt (B / b)) * q / (d * e) := by
      field_simp

    _ = _ := by rw [hs]

theorem actual_middle_radial_block_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ B N M : ℝ) (_hD₁ : 1 ≤ D₁) (_hD₂ : 1 ≤ D₂) (_hB : 1 ≤ B) (_hN : 1 ≤ N) (_hM : 0 < M)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
        (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
        (_hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
        (_hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (h : O), h ≠ 0 →
        (1 + Real.sqrt (M / B) * ‖eisEmbedding h‖ ^ 2 / (D₁ * D₂)) ^ A *
          (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
            originalTerm rows left right a b D.val E.val i j k *
              paperRadialFourier W
                (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
                  ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  obtain ⟨C, hC, hb⟩ := canonical_original_radial_divisor_block_bound W 4 0 0 (by norm_num) (by norm_num) (by norm_num) A
  refine ⟨C, hC, ?_⟩
  intro m n p _ _ _ _ _ _ ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT rows left right hr hl hri hrows hleft hright a b h hh
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hB0 : 0 < B := by linarith
  let R := Real.sqrt (M / B) * ‖eisEmbedding h‖ ^ 2 / (D₁ * D₂)
  have hR : 0 < R := div_pos (mul_pos (Real.sqrt_pos.mpr (div_pos hM hB0))
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)))) (mul_pos hD₁0 hD₂0)
  let x : S → T → m → ℝ := fun D E i => Real.log
    (middleRatio B (Ideal.absNorm (rows i)) D₁ (Ideal.absNorm D.val) D₂ (Ideal.absNorm E.val))
  have hx (D : S) (E : T) (i : m) : |x D E i| ≤ 4 :=
    middleRatio_log_bound _ (middleRatio_bounds _ _ _ _ _ _ hB0 (hrows i).2 hD₁0
      (hS D.val D.property) hD₂0 (hT E.val E.property))
  have he := hb R hR ε hε S T D₁ D₂ B N hD₁ hD₂ hN hS hT rows left right hr hl hri
    (fun i => ⟨(hrows i).1, (hrows i).2.2⟩) hleft hright a b x (fun _ => 0) (fun _ => 0) hx
    (fun _ => by simp) (fun _ => by simp)
  have harg (D : S) (E : T) (i : m) : R * Real.exp (x D E i + (0 + 0)) =
      Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)) := by
    simp only [add_zero]
    exact middleRatio_argument _ _ _ _ _ _ _ _ hM hB0 (hrows i).2 hD₁0
      (hS D.val D.property) hD₂0 (hT E.val E.property)
  simpa only [harg, R] using he

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def residualPairWeight (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (S T : Finset ι) : ℂ :=
  star (supportMobius (fun i => Ideal.span {p i}) S * secondInputCoefficient p hg Ψ₁ m c d H₁ S) *
    (supportMobius (fun i => Ideal.span {p i}) T * secondInputCoefficient p hg Ψ₂ m c d H₂ T)

def residualTailCost (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m c d : O) (H₁ H₂ : Finset ι → ℂ) (e : O) (Y H : ℝ) (A : ℕ) (P : ℝ) : ℝ :=
  ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset, if Disjoint S T then
    let n := ∏ i : activeSupport T S, p i.val
    let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
    ‖residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T‖ *
      ((Y/‖eisEmbedding n‖) * (P / ((min 1 scale)^2 * (1+H)^A)))
    else 0

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def boundedPrimeSupports (F : Finset ι) (X : ℝ) : Finset (Finset ι) :=
  F.powerset.filter (fun S => primeProductNorm p S ≤ X)

end SecondPassArithmetic

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem column_sqrt_ratio_bounds (N n : ℝ) (hN : 0 < N) (hn : N / 2 ≤ n ∧ n ≤ N) :
    1 / 4 ≤ Real.sqrt (n / N) ∧ Real.sqrt (n / N) ≤ 2 := by
  have hq0 : 0 ≤ n / N := div_nonneg (by linarith) hN.le
  have hq1 : (1 / 2 : ℝ) ≤ n / N := (le_div_iff₀ hN).mpr (by linarith)
  have hq2 : n / N ≤ 1 := (div_le_one hN).mpr hn.2
  have hs := Real.sq_sqrt hq0
  have hp := Real.sqrt_nonneg (n / N)
  constructor <;> nlinarith

theorem dual_middle_sqrt_identity (M B b N i j F : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : 0 < b) (hN : 0 < N)
    (hi : 0 < i) (hj : 0 < j) (hF : 0 < F) :
    N * Real.sqrt (F / (M * B)) * Real.sqrt (B / b) * Real.sqrt (i / N) * Real.sqrt (j / N) =
      Real.sqrt (F * i * j / (M * b)) := by
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  simp only [mul_pow, Real.sq_sqrt (show 0 ≤ F / (M * B) by positivity),
    Real.sq_sqrt (show 0 ≤ B / b by positivity), Real.sq_sqrt (show 0 ≤ i / N by positivity),
    Real.sq_sqrt (show 0 ≤ j / N by positivity), Real.sq_sqrt (show 0 ≤ F * i * j / (M * b) by positivity)]
  field_simp

theorem dual_middle_argument (M B b N i j F D₁ d D₂ e q : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b ∧ b ≤ B) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) (hF : 0 < F)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d ∧ d ≤ 2 * D₁)
    (hD₂ : 0 < D₂) (he : D₂ ≤ e ∧ e ≤ 2 * D₂) :
    (N * Real.sqrt (F / (M * B)) * q / (D₁ * D₂)) *
      Real.exp (Real.log (middleRatio B b D₁ d D₂ e) +
        (Real.log (Real.sqrt (i / N)) + Real.log (Real.sqrt (j / N)))) =
      Real.sqrt (F * i * j / (M * b)) * q / (d * e) := by
  have hb0 : 0 < b := by linarith
  have hi0 : 0 < i := by linarith
  have hj0 : 0 < j := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd.1
  have he0 : 0 < e := hD₂.trans_le he.1
  have hr : 0 < middleRatio B b D₁ d D₂ e := by
    have hh := middleRatio_bounds B b D₁ d D₂ e hB hb hD₁ hd hD₂ he
    linarith
  rw [Real.exp_add, Real.exp_add, Real.exp_log hr,
    Real.exp_log (Real.sqrt_pos.mpr (div_pos hi0 hN)),
    Real.exp_log (Real.sqrt_pos.mpr (div_pos hj0 hN))]
  unfold middleRatio
  calc
    _ = (N * Real.sqrt (F / (M * B)) * Real.sqrt (B / b) * Real.sqrt (i / N) * Real.sqrt (j / N)) * q / (d * e) := by
      field_simp

    _ = _ := by rw [dual_middle_sqrt_identity M B b N i j F hM hB hb0 hN hi0 hj0 hF]

theorem actual_dual_middle_radial_block_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ B N M F : ℝ) (_hD₁ : 1 ≤ D₁) (_hD₂ : 1 ≤ D₂) (_hB : 1 ≤ B) (_hN : 1 ≤ N)
        (_hM : 0 < M) (_hF : 0 < F)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
        (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
        (_hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
        (_hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (h : O), h ≠ 0 →
        (1 + N * Real.sqrt (F / (M * B)) * ‖eisEmbedding h‖ ^ 2 / (D₁ * D₂)) ^ A *
          (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
            originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
              (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
                (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
                  ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  obtain ⟨C, hC, hb⟩ := canonical_original_radial_divisor_block_bound W 4 4 4 (by norm_num) (by norm_num) (by norm_num) A
  refine ⟨C, hC, ?_⟩
  intro m n p _ _ _ _ _ _ ε hε S T D₁ D₂ B N M F hD₁ hD₂ hB hN hM hF hS hT rows left right hr hl hri hrows hleft hright a b h hh
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hB0 : 0 < B := by linarith
  have hN0 : 0 < N := by linarith
  let R := N * Real.sqrt (F / (M * B)) * ‖eisEmbedding h‖ ^ 2 / (D₁ * D₂)
  have hR : 0 < R := div_pos (mul_pos (mul_pos hN0 (Real.sqrt_pos.mpr (by positivity)))
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)))) (mul_pos hD₁0 hD₂0)
  let x : S → T → m → ℝ := fun D E i => Real.log
    (middleRatio B (Ideal.absNorm (rows i)) D₁ (Ideal.absNorm D.val) D₂ (Ideal.absNorm E.val))
  let y : n → ℝ := fun j => Real.log (Real.sqrt ((Ideal.absNorm (left j) : ℝ) / N))
  let z : p → ℝ := fun k => Real.log (Real.sqrt ((Ideal.absNorm (right k) : ℝ) / N))
  have hx (D : S) (E : T) (i : m) : |x D E i| ≤ 4 :=
    middleRatio_log_bound _ (middleRatio_bounds _ _ _ _ _ _ hB0 (hrows i).2 hD₁0
      (hS D.val D.property) hD₂0 (hT E.val E.property))
  have hy (j : n) : |y j| ≤ 4 := middleRatio_log_bound _ (column_sqrt_ratio_bounds N _ hN0 (hleft j).2)
  have hz (k : p) : |z k| ≤ 4 := middleRatio_log_bound _ (column_sqrt_ratio_bounds N _ hN0 (hright k).2)
  have he := hb R hR ε hε S T D₁ D₂ B N hD₁ hD₂ hN hS hT rows left right hr hl hri
    (fun i => ⟨(hrows i).1, (hrows i).2.2⟩) (fun j => ⟨(hleft j).1, (hleft j).2.2⟩)
    (fun k => ⟨(hright k).1, (hright k).2.2⟩) a b x y z hx hy hz
  have harg (D : S) (E : T) (i : m) (j : n) (k : p) : R * Real.exp (x D E i + (y j + z k)) =
      Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
        (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)) :=
    dual_middle_argument _ _ _ _ _ _ _ _ _ _ _ _ hM hB0 (hrows i).2 hN0 (hleft j).2 (hright k).2 hF
      hD₁0 (hS D.val D.property) hD₂0 (hT E.val E.property)
  simpa only [harg, R] using he

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a : n → ℂ) (b : p → ℂ) (h : O) (hh : h ≠ 0)

include hD₁ hD₂ hB hN hM hS hT hr hl hri hrows hh

end CanonicalQuadraticSieve

open Filter
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma abs_le_inv_of_mul_sq_le_one {v t : ℝ} (hv : 0<v) (h : v^2*t^2≤1) :
    |t|≤1/v := by
  apply (le_div_iff₀ hv).mpr
  have he : |v*t|≤1 := (sq_le_one_iff_abs_le_one _).mp (by simpa only [mul_pow] using h)
  simpa only [abs_mul,abs_of_pos hv,mul_comm] using he

lemma heightLog_first_bounds (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C ^2) (hv : 0<v)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    |heightLogDx A B C D x y v|≤1/v ∧
    |heightLogDy A B C D x y v|≤1/v ∧
    |heightLogDv A B C D x y v|≤1/v := by
  have he := heightLog_eikonal A B C D x y v hrel hv.ne' hq
  have hx := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDx A B C D x y v))
  have hy := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDy A B C D x y v))
  have hz := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDv A B C D x y v))
  exact ⟨abs_le_inv_of_mul_sq_le_one hv (by nlinarith),
    abs_le_inv_of_mul_sq_le_one hv (by nlinarith),
    abs_le_inv_of_mul_sq_le_one hv (by nlinarith)⟩

lemma heightLog_second_bounds (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C ^2) (hv : 0<v)
    (hA : 0≤A) (hq : 0<quadraticHeightDenominator A B C D x y v)
    (hAv : A*v^2≤quadraticHeightDenominator A B C D x y v) :
    |heightLogDxx A B C D x y v|≤7/v^2 ∧
    |heightLogDyy A B C D x y v|≤7/v^2 ∧
    |heightLogDvv A B C D x y v|≤7/v^2 := by
  let q := quadraticHeightDenominator A B C D x y v
  let r := v^2*A/q
  have hr0 : 0≤ r := div_nonneg (mul_nonneg (sq_nonneg v) hA) hq.le
  have hr1 : r≤1 := (div_le_one hq).mpr (by simpa only [mul_comm] using hAv)
  have he := heightLog_eikonal A B C D x y v hrel hv.ne' hq.ne'
  have hx := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDx A B C D x y v))
  have hy := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDy A B C D x y v))
  have hz := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDv A B C D x y v))
  have hx1 : v^2*(heightLogDx A B C D x y v)^2≤1 := by nlinarith
  have hy1 : v^2*(heightLogDy A B C D x y v)^2≤1 := by nlinarith
  have hxx : v^2*heightLogDxx A B C D x y v =
      v^2*(heightLogDx A B C D x y v)^2-2*r := by
    dsimp [heightLogDxx,heightLogDx,r,q]
    field_simp
    ; ring
  have hyy : v^2*heightLogDyy A B C D x y v =
      v^2*(heightLogDy A B C D x y v)^2-2*r := by
    dsimp [heightLogDyy,heightLogDy,r,q]
    field_simp
    ; ring
  have hvv : v^2*heightLogDvv A B C D x y v = -1-2*r+4*r^2 := by
    dsimp [heightLogDvv,r,q]
    field_simp [hv.ne',hq.ne']
    ; ring
  have hconv (a : ℝ) (ha : |v^2*a|≤7) : |a|≤7/v^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hv)).mpr
    simpa only [abs_mul,abs_of_nonneg (sq_nonneg v),mul_comm] using ha
  refine ⟨hconv _ (abs_le.mpr ⟨?_,?_⟩), hconv _ (abs_le.mpr ⟨?_,?_⟩),
    hconv _ (abs_le.mpr ⟨?_,?_⟩)⟩
  all_goals nlinarith [sq_nonneg r,mul_nonneg hr0 (sub_nonneg.mpr hr1)]

lemma actual_quadraticHeight_nonneg (u : Fin 2 → ℂ) (x y v : ℝ) :
    Complex.normSq (u 0)*v^2 ≤
      quadraticHeightDenominator (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
        (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) x y v := by
  rw [← heightDenominator_eq_quadratic]
  unfold heightDenominator
  rw [Complex.normSq_eq_norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

open Filter
open scoped BigOperators Classical Topology Matrix

abbrev SpatialCoordinates := Fin 3 → ℝ

def axisSlice (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) (j : Fin 3) : ℝ → ℂ :=
  fun t => f (Function.update p j t)

def spatialLogD (A B C D : ℝ) (p : SpatialCoordinates) : Fin 3 → ℝ :=
  ![heightLogDx A B C D (p 0) (p 1) (p 2),
    heightLogDy A B C D (p 0) (p 1) (p 2),
    heightLogDv A B C D (p 0) (p 1) (p 2)]
def spatialLogDD (A B C D : ℝ) (p : SpatialCoordinates) : Fin 3 → ℝ :=
  ![heightLogDxx A B C D (p 0) (p 1) (p 2),
    heightLogDyy A B C D (p 0) (p 1) (p 2),
    heightLogDvv A B C D (p 0) (p 1) (p 2)]

lemma spatial_axis_hasDerivAt (s : ℂ) (A B C D : ℝ) (p : SpatialCoordinates) (j : Fin 3)
    (hv : p 2≠0) (hq : quadraticHeightDenominator A B C D (p 0) (p 1) (p 2)≠0) :
    HasDerivAt (axisSlice (fun q => spatialHeightPower s A B C D (q 0) (q 1) (q 2)) p j)
      (spatialHeightPower s A B C D (p 0) (p 1) (p 2)*s*(spatialLogD A B C D p j:ℂ)) (p j) := by
  unfold axisSlice
  fin_cases j
  · have h := hasDerivAt_logRatioPower s (hasDerivAt_const (p 0) (p 2))
      (quadraticHeightDenominator_hasDerivAt_x A B C D (p 0) (p 1) (p 2)) hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,heightLogDx] using h
  · have h := hasDerivAt_logRatioPower s (hasDerivAt_const (p 1) (p 2))
      (quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) (p 1) (p 2)) hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,heightLogDy] using h
  · have h := hasDerivAt_logRatioPower s (hasDerivAt_id (p 2))
      (quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) (p 2)) hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,heightLogDv] using h

lemma spatial_axis_hasDerivAt_deriv (s : ℂ) (A B C D : ℝ) (p : SpatialCoordinates) (j : Fin 3)
    (hv : p 2≠0) (hq : quadraticHeightDenominator A B C D (p 0) (p 1) (p 2)≠0) :
    HasDerivAt (deriv (axisSlice (fun q => spatialHeightPower s A B C D (q 0) (q 1) (q 2)) p j))
      (spatialHeightPower s A B C D (p 0) (p 1) (p 2)*
        (s^2*(spatialLogD A B C D p j:ℂ)^2+s*(spatialLogDD A B C D p j:ℂ))) (p j) := by
  unfold axisSlice
  fin_cases j
  · have h := hasDerivAt_deriv_logRatioPower s (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D t (p 1) (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+B)) (p 0) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_x A B C D t (p 1) (p 2))
      (hasDerivAt_const (p 0) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 0)).const_mul A |>.add_const B).const_mul 2)
      hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,spatialLogDD,heightLogDx,heightLogDxx] using h
  · have h := hasDerivAt_deriv_logRatioPower s (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D (p 0) t (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+C)) (p 1) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) t (p 2))
      (hasDerivAt_const (p 1) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 1)).const_mul A |>.add_const C).const_mul 2)
      hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,spatialLogDD,heightLogDy,heightLogDyy] using h
  · have h := hasDerivAt_deriv_logRatioPower s (fun t => t)
      (fun t => quadraticHeightDenominator A B C D (p 0) (p 1) t) (fun _ => 1)
      (fun t => 2*A*t) (p 2) 0 (2*A)
      (fun t => hasDerivAt_id t)
      (fun t => quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) t)
      (hasDerivAt_const (p 2) 1)
      (by simpa only [id_eq,mul_one] using (hasDerivAt_id (p 2)).const_mul (2*A))
      hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,spatialLogDD,heightLogDv,heightLogDvv,div_eq_mul_inv] using h

def rowSmoothPower (s : ℂ) (u : Fin 2 → ℂ) (p : SpatialCoordinates) : ℂ :=
  spatialHeightPower s (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2)

def rowLogD (u : Fin 2 → ℂ) (p : SpatialCoordinates) (j : Fin 3) : ℝ :=
  spatialLogD (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) p j

def rowLogDD (u : Fin 2 → ℂ) (p : SpatialCoordinates) (j : Fin 3) : ℝ :=
  spatialLogDD (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) p j

lemma row_denominator_pos (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hv : 0<p 2) :
    0 < quadraticHeightDenominator (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
      (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2) := by
  rw [← heightDenominator_eq_quadratic]
  exact heightDenominator_pos _ _ hv u hu

lemma rowLogD_bound (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    |rowLogD u p j| ≤ 1/(p 2) := by
  have h := heightLog_first_bounds _ _ _ _ (p 0) (p 1) (p 2)
    (complex_row_quadratic_relation (u 0) (u 1)) hv (row_denominator_pos u hu p hv).ne'
  fin_cases j <;> simp only [rowLogD,spatialLogD,]
  · exact h.1
  · exact h.2.1
  · exact h.2.2

lemma rowLogDD_bound (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    |rowLogDD u p j| ≤ 7/(p 2)^2 := by
  have h := heightLog_second_bounds _ _ _ _ (p 0) (p 1) (p 2)
    (complex_row_quadratic_relation (u 0) (u 1)) hv (Complex.normSq_nonneg _)
    (row_denominator_pos u hu p hv) (actual_quadraticHeight_nonneg u (p 0) (p 1) (p 2))
  fin_cases j <;> simp only [rowLogDD,spatialLogDD,]
  · exact h.1
  · exact h.2.1
  · exact h.2.2

lemma row_axis_hasDerivAt (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    HasDerivAt (axisSlice (rowSmoothPower s u) p j)
      (rowSmoothPower s u p*s*(rowLogD u p j:ℂ)) (p j) :=
  spatial_axis_hasDerivAt _ _ _ _ _ p j hv.ne' (row_denominator_pos u hu p hv).ne'

lemma row_axis_hasDerivAt_deriv (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    HasDerivAt (deriv (axisSlice (rowSmoothPower s u) p j))
      (rowSmoothPower s u p*(s^2*(rowLogD u p j:ℂ)^2+s*(rowLogDD u p j:ℂ))) (p j) :=
  spatial_axis_hasDerivAt_deriv _ _ _ _ _ p j hv.ne' (row_denominator_pos u hu p hv).ne'

end CubicEisenstein

open Filter
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma hasDerivAt_deriv_tsum_of_bounds {ι : Type*} (f : ι → ℝ → ℂ)
    (M₁ M₂ : ι → ℝ) (U : Set ℝ) (x : ℝ)
    (hU : IsOpen U) (hUc : IsPreconnected U) (hx : x ∈ U)
    (hM₁ : Summable M₁) (hM₂ : Summable M₂)
    (hfirst : ∀i y, y∈U → DifferentiableAt ℝ (f i) y)
    (hsecond : ∀i y, y∈U → DifferentiableAt ℝ (deriv (f i)) y)
    (hbound₁ : ∀i y, y∈U → ‖deriv (f i) y‖≤M₁ i)
    (hbound₂ : ∀i y, y∈U → ‖deriv (deriv (f i)) y‖≤M₂ i)
    (hsum : Summable (fun i => f i x)) :
    HasDerivAt (deriv (fun y => ∑'i,f i y)) (∑'i,deriv (deriv (f i)) x) x := by
  have hfirstSum (y : ℝ) (hy : y∈U) :=
    hasDerivAt_tsum_of_isPreconnected hM₁ hU hUc
      (fun i z hz => (hfirst i z hz).hasDerivAt) hbound₁ hx hsum hy
  have hsumFirst : Summable (fun i => deriv (f i) x) :=
    Summable.of_norm_bounded hM₁ (fun i => hbound₁ i x hx)
  have hsecondSum := hasDerivAt_tsum_of_isPreconnected hM₂ hU hUc
    (fun i z hz => (hsecond i z hz).hasDerivAt) hbound₂ hx hsumFirst hx
  apply hsecondSum.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact (hfirstSum y hy).deriv

lemma norm_row_axis_deriv (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ‖deriv (axisSlice (rowSmoothPower s u) p j) (p j)‖ ≤
      ‖rowSmoothPower s u p‖ * (‖s‖ * (1/(p 2))) := by
  rw [(row_axis_hasDerivAt s u hu p hv j).deriv,norm_mul,norm_mul,
    Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ ‖rowSmoothPower s u p‖*‖s‖*(1/(p 2)) :=
      mul_le_mul_of_nonneg_left (rowLogD_bound u hu p hv j) (by positivity)
    _ = _ := by ring

lemma norm_row_axis_deriv2 (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ‖deriv (deriv (axisSlice (rowSmoothPower s u) p j)) (p j)‖ ≤
      ‖rowSmoothPower s u p‖ * (‖s‖^2 * (1/(p 2))^2 + ‖s‖ * (7/(p 2)^2)) := by
  rw [(row_axis_hasDerivAt_deriv s u hu p hv j).deriv,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ‖s^2*(rowLogD u p j:ℂ)^2‖+‖s*(rowLogDD u p j:ℂ)‖ := norm_add_le _ _
    _ = ‖s‖^2*|rowLogD u p j|^2 + ‖s‖*|rowLogDD u p j| := by
      simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ _ := by
      have hfirst := rowLogD_bound u hu p hv j
      have hsecond := rowLogDD_bound u hu p hv j
      gcongr

def smoothSummand (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates) : ℂ :=
  (cosetCharacter r)⁻¹ * rowSmoothPower s (embeddedRow r) p

lemma smoothSummand_eq_actual (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothSummand s r p =
      summand (upperSection ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hv) s r := by
  rw [smoothSummand,← eigenfunction_summand_eq_actual_series]
  congr 1
  exact (actualHeightPower_eq_spatial s (embeddedRow r) (embeddedRow_ne_zero r)
    (p 0) (p 1) (p 2) hv).symm

lemma smooth_axis_differentiable (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (axisSlice (smoothSummand s r) p j) (p j) :=
  ((row_axis_hasDerivAt s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).const_mul _).differentiableAt

lemma smooth_axis_deriv_differentiable (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (deriv (axisSlice (smoothSummand s r) p j)) (p j) := by
  change DifferentiableAt ℝ (deriv (fun t => (cosetCharacter r)⁻¹ *
    axisSlice (rowSmoothPower s (embeddedRow r)) p j t)) (p j)
  rw [deriv_const_mul_field']
  exact ((row_axis_hasDerivAt_deriv s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).const_mul _).differentiableAt

lemma norm_smooth_axis_deriv (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ‖deriv (axisSlice (smoothSummand s r) p j) (p j)‖ ≤
      ‖smoothSummand s r p‖ * (‖s‖ * (1/(p 2))) := by
  have h := norm_row_axis_deriv s (embeddedRow r) (embeddedRow_ne_zero r) p hv j
  unfold axisSlice at h ⊢
  simpa only [smoothSummand,deriv_const_mul_field,norm_mul,norm_inv,
    norm_cosetCharacter,inv_one,one_mul] using h

lemma norm_smooth_axis_deriv2 (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ‖deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)‖ ≤
      ‖smoothSummand s r p‖ * (‖s‖^2 * (1/(p 2))^2 + ‖s‖ * (7/(p 2)^2)) := by
  have h := norm_row_axis_deriv2 s (embeddedRow r) (embeddedRow_ne_zero r) p hv j
  unfold axisSlice at h ⊢
  simpa only [smoothSummand,deriv_const_mul_field',deriv_const_mul_field,norm_mul,norm_inv,
    norm_cosetCharacter,inv_one,one_mul] using h

lemma smoothSummand_axis_update (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates)
    (j : Fin 3) (t : ℝ) :
    axisSlice (smoothSummand s r) (Function.update p j t) j =
      axisSlice (smoothSummand s r) p j := by
  funext z
  simp only [axisSlice,Function.update_idem]

end CubicEisenstein

open Filter
open scoped BigOperators Classical Topology

namespace CubicEisenstein

def clampedCoordinates (deltaLoss : ℝ) (hδ : 0<deltaLoss) (p : SpatialCoordinates) : UpperCoordinates :=
  ⟨((p 0:ℂ)+(p 1:ℂ)*Complex.I,max deltaLoss (p 2)),lt_of_lt_of_le hδ (le_max_left _ _)⟩

lemma continuous_clampedCoordinates (deltaLoss : ℝ) (hδ : 0<deltaLoss) :
    Continuous (clampedCoordinates deltaLoss hδ) := by
  apply Continuous.subtype_mk
  exact ((Complex.continuous_ofReal.comp (continuous_apply 0)).add
    ((Complex.continuous_ofReal.comp (continuous_apply 1)).mul_const Complex.I)).prodMk
      (continuous_const.max (continuous_apply 2))

lemma continuous_axis_update (p : SpatialCoordinates) (j : Fin 3) :
    Continuous (fun t : ℝ => Function.update p j t) := by
  apply continuous_pi
  intro k
  by_cases h : k=j
  · subst k
    simp only [Function.update_self]
    fun_prop
  · simpa only [Function.update_of_ne h] using (continuous_const : Continuous (fun _ : ℝ => p k))

lemma smoothSummand_eq_clamped (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates)
    (deltaLoss : ℝ) (hδ : 0<deltaLoss) (hp : deltaLoss≤p 2) :
    smoothSummand s r p = summand (coordinateSection (clampedCoordinates deltaLoss hδ p)) s r := by
  have hv : 0<p 2 := lt_of_lt_of_le hδ hp
  simpa only [coordinateSection,clampedCoordinates,max_eq_right hp] using smoothSummand_eq_actual s r p hv

theorem axis_summable_derivative_bounds (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ∃ ε : ℝ, 0<ε ∧ ∃ M₀ M₁ M₂ : CuspCosets → ℝ,
      Summable M₀ ∧ Summable M₁ ∧ Summable M₂ ∧
      ∀ t ∈ Metric.ball (p j) ε,
        0 < (Function.update p j t) 2 ∧ ∀ r : CuspCosets,
        ‖axisSlice (smoothSummand s r) p j t‖≤M₀ r ∧
        ‖deriv (axisSlice (smoothSummand s r) p j) t‖≤M₁ r ∧
        ‖deriv (deriv (axisSlice (smoothSummand s r) p j)) t‖≤M₂ r := by
  let deltaLoss : ℝ := p 2/2
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let path := fun t => clampedCoordinates deltaLoss hδ (Function.update p j t)
  have hpath : Continuous path := (continuous_clampedCoordinates deltaLoss hδ).comp (continuous_axis_update p j)
  let C := rowBound (coordinateSection (path (p j)))+1
  have hC : 0<C := by dsimp [C]; linarith [rowBound_pos (coordinateSection (path (p j)))]
  have hb : ∀ᶠ t in 𝓝 (p j), rowBound (coordinateSection (path t))<C :=
    (continuous_coordinate_rowBound.comp hpath).continuousAt.eventually_lt_const (by dsimp [C]; linarith)
  have hh : ∀ᶠ t in 𝓝 (p j), deltaLoss < (Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    change deltaLoss < (Function.update p j (p j)) 2
    rw [Function.update_eq_self]
    dsimp [deltaLoss]
    linarith
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff_ball.mp (hh.and hb)
  obtain ⟨M,hM,hMnonneg,hbound⟩ := coordinate_summable_majorant C s.re s.re hC hs hs
  let c₁ := ‖s‖*(1/deltaLoss)
  let c₂ := ‖s‖^2*(1/deltaLoss)^2 + ‖s‖*(7/deltaLoss^2)
  refine ⟨ε,hε,M,fun r => M r*c₁,fun r => M r*c₂,hM,hM.mul_right _,hM.mul_right _,?_⟩
  intro t ht
  obtain ⟨hht,hbt⟩ := hball t ht
  have hpos : 0 < (Function.update p j t) 2 := lt_trans hδ hht
  refine ⟨hpos,fun r => ?_⟩
  have hm : ‖smoothSummand s r (Function.update p j t)‖≤M r := by
    rw [smoothSummand_eq_clamped s r _ deltaLoss hδ hht.le]
    exact hbound (path t,s) hbt.le le_rfl le_rfl r
  have hfrac : 1 / (Function.update p j t) 2 ≤ 1/deltaLoss := one_div_le_one_div_of_le hδ hht.le
  have hfrac₂ : 7 / ((Function.update p j t) 2)^2 ≤ 7/deltaLoss^2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ)
    nlinarith
  have hd₁ := norm_smooth_axis_deriv s r (Function.update p j t) hpos j
  have hd₂ := norm_smooth_axis_deriv2 s r (Function.update p j t) hpos j
  rw [smoothSummand_axis_update,Function.update_self] at hd₁ hd₂
  refine ⟨hm,hd₁.trans ?_,hd₂.trans ?_⟩
  · apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    exact mul_le_mul_of_nonneg_left hfrac (norm_nonneg s)
  · apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    dsimp [c₂]
    gcongr

lemma smooth_axis_differentiable_at (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) (hv : 0<(Function.update p j t) 2) :
    DifferentiableAt ℝ (axisSlice (smoothSummand s r) p j) t := by
  have h := smooth_axis_differentiable s r (Function.update p j t) hv j
  simpa only [smoothSummand_axis_update,Function.update_self] using h

lemma smooth_axis_deriv_differentiable_at (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) (hv : 0<(Function.update p j t) 2) :
    DifferentiableAt ℝ (deriv (axisSlice (smoothSummand s r) p j)) t := by
  have h := smooth_axis_deriv_differentiable s r (Function.update p j t) hv j
  simpa only [smoothSummand_axis_update,Function.update_self] using h

end CubicEisenstein

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open Filter
open scoped BigOperators Classical Topology Matrix

def smoothEisenstein (s : ℂ) (p : SpatialCoordinates) : ℂ := ∑'r, smoothSummand s r p

lemma smoothEisenstein_eq_actual (s : ℂ) (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothEisenstein s p = upperEisenstein ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hv s := by
  unfold smoothEisenstein upperEisenstein eisenstein
  exact tsum_congr (fun r => smoothSummand_eq_actual s r p hv)

theorem eisenstein_axis_termwise (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    Summable (fun r => deriv (axisSlice (smoothSummand s r) p j) (p j)) ∧
    Summable (fun r => deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)) ∧
    HasDerivAt (axisSlice (smoothEisenstein s) p j)
      (∑'r,deriv (axisSlice (smoothSummand s r) p j) (p j)) (p j) ∧
    HasDerivAt (deriv (axisSlice (smoothEisenstein s) p j))
      (∑'r,deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)) (p j) := by
  obtain ⟨ε,hε,M₀,M₁,M₂,hM₀,hM₁,hM₂,hbound⟩ := axis_summable_derivative_bounds s hs p hv j
  have hx : p j ∈ Metric.ball (p j) ε := Metric.mem_ball_self hε
  have hs₀ : Summable (fun r => axisSlice (smoothSummand s r) p j (p j)) :=
    Summable.of_norm_bounded hM₀ (fun r => ((hbound (p j) hx).2 r).1)
  have hs₁ : Summable (fun r => deriv (axisSlice (smoothSummand s r) p j) (p j)) :=
    Summable.of_norm_bounded hM₁ (fun r => ((hbound (p j) hx).2 r).2.1)
  have hs₂ : Summable (fun r => deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)) :=
    Summable.of_norm_bounded hM₂ (fun r => ((hbound (p j) hx).2 r).2.2)
  have hd₁ (r : CuspCosets) (t : ℝ) (ht : t∈Metric.ball (p j) ε) :
      DifferentiableAt ℝ (axisSlice (smoothSummand s r) p j) t :=
    smooth_axis_differentiable_at s r p j t (hbound t ht).1
  have hd₂ (r : CuspCosets) (t : ℝ) (ht : t∈Metric.ball (p j) ε) :
      DifferentiableAt ℝ (deriv (axisSlice (smoothSummand s r) p j)) t :=
    smooth_axis_deriv_differentiable_at s r p j t (hbound t ht).1
  refine ⟨hs₁,hs₂,?_,?_⟩
  · exact hasDerivAt_tsum_of_isPreconnected hM₁ Metric.isOpen_ball Metric.isPreconnected_ball
      (fun r t ht => (hd₁ r t ht).hasDerivAt) (fun r t ht => ((hbound t ht).2 r).2.1) hx hs₀ hx
  · exact hasDerivAt_deriv_tsum_of_bounds (fun r => axisSlice (smoothSummand s r) p j)
      M₁ M₂ _ (p j) Metric.isOpen_ball Metric.isPreconnected_ball hx hM₁ hM₂ hd₁ hd₂
      (fun r t ht => ((hbound t ht).2 r).2.1) (fun r t ht => ((hbound t ht).2 r).2.2) hs₀

def axisLaplacian (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) : ℂ :=
  (p 2:ℂ)^2 * (∑ j : Fin 3, deriv (deriv (axisSlice f p j)) (p j)) -
    (p 2:ℂ)*deriv (axisSlice f p 2) (p 2)

lemma axisSlice_zero (f : ℝ → ℝ → ℝ → ℂ) (p : SpatialCoordinates) :
    axisSlice (fun q => f (q 0) (q 1) (q 2)) p 0 = fun t => f t (p 1) (p 2) := by
  funext t
  simp [axisSlice,Function.update]
lemma axisSlice_one (f : ℝ → ℝ → ℝ → ℂ) (p : SpatialCoordinates) :
    axisSlice (fun q => f (q 0) (q 1) (q 2)) p 1 = fun t => f (p 0) t (p 2) := by
  funext t
  simp [axisSlice,Function.update]
lemma axisSlice_two (f : ℝ → ℝ → ℝ → ℂ) (p : SpatialCoordinates) :
    axisSlice (fun q => f (q 0) (q 1) (q 2)) p 2 = fun t => f (p 0) (p 1) t := by
  funext t
  simp [axisSlice,Function.update]

lemma axisLaplacian_eq_hyperbolicLaplacian (f : ℝ → ℝ → ℝ → ℂ) (p : SpatialCoordinates) :
    axisLaplacian (fun q => f (q 0) (q 1) (q 2)) p =
      hyperbolicLaplacian f (p 0) (p 1) (p 2) := by
  simp only [axisLaplacian,Fin.sum_univ_three,axisSlice_zero,axisSlice_one,axisSlice_two,
    hyperbolicLaplacian]

lemma smoothSummand_axisLaplacian (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates) (hv : 0<p 2) :
    axisLaplacian (smoothSummand s r) p = s*(s-2)*smoothSummand s r p := by
  unfold smoothSummand rowSmoothPower
  rw [axisLaplacian_eq_hyperbolicLaplacian
    (fun x y v => (cosetCharacter r)⁻¹ *
      spatialHeightPower s (Complex.normSq (embeddedRow r 0))
        ((embeddedRow r 0*star (embeddedRow r 1)).re)
        (-(embeddedRow r 0*star (embeddedRow r 1)).im)
        (Complex.normSq (embeddedRow r 1)) x y v) p,
    hyperbolicLaplacian_const_mul,spatialHeightPower_eigenfunction]
  · ring
  · exact complex_row_quadratic_relation _ _
  · exact hv.ne'
  · exact (row_denominator_pos _ (embeddedRow_ne_zero r) p hv).ne'

theorem smoothEisenstein_eigenfunction (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    axisLaplacian (smoothEisenstein s) p = s*(s-2)*smoothEisenstein s p := by
  have hterms := eisenstein_axis_termwise s hs p hv
  let second := fun (j : Fin 3) (r : CuspCosets) =>
    deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)
  let first := fun r : CuspCosets => deriv (axisSlice (smoothSummand s r) p 2) (p 2)
  have hsecond (j : Fin 3) : Summable (second j) := (hterms j).2.1
  have hfirst : Summable first := (hterms 2).1
  have hsum : Summable (fun r => ∑ j : Fin 3, second j r) := by
    simpa only [Fin.sum_univ_three] using ((hsecond 0).add (hsecond 1)).add (hsecond 2)
  have hcomm : (∑ j : Fin 3, ∑'r,second j r) = ∑'r,∑ j : Fin 3,second j r := by
    exact (Summable.tsum_finsetSum (fun j _ => hsecond j)).symm
  unfold axisLaplacian
  simp_rw [fun j => (hterms j).2.2.2.deriv]
  rw [(hterms 2).2.2.1.deriv]
  change (p 2:ℂ)^2*(∑j : Fin 3,∑'r,second j r) - (p 2:ℂ)*(∑'r,first r) = _
  rw [hcomm,← tsum_mul_left,← tsum_mul_left,← (hsum.mul_left _).tsum_sub (hfirst.mul_left _)]
  change (∑'r,axisLaplacian (smoothSummand s r) p) = _
  simp_rw [smoothSummand_axisLaplacian s _ p hv]
  rw [tsum_mul_left]
  rfl

lemma axisSlice_eventuallyEq_of_positive (f g : SpatialCoordinates → ℂ)
    (heq : ∀ q, 0<q 2 → f q=g q) (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    axisSlice f p j =ᶠ[𝓝 (p j)] axisSlice g p j := by
  have hnear : ∀ᶠ t in 𝓝 (p j), 0<(Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    change 0<(Function.update p j (p j)) 2
    simpa only [Function.update_eq_self] using hv
  filter_upwards [hnear] with t ht
  exact heq _ ht

lemma axisLaplacian_congr_positive (f g : SpatialCoordinates → ℂ)
    (heq : ∀ q, 0<q 2 → f q=g q) (p : SpatialCoordinates) (hv : 0<p 2) :
    axisLaplacian f p = axisLaplacian g p := by
  have h (j : Fin 3) := axisSlice_eventuallyEq_of_positive f g heq p hv j
  unfold axisLaplacian
  rw [(h 2).deriv_eq]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  exact (h j).deriv.deriv_eq

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

lemma positive_ideal_dyadic_exists (N : ℝ) (D : Ideal O)
    (hD : 1 ≤ (Ideal.absNorm D : ℝ)) (hDN : (Ideal.absNorm D : ℝ) ≤ N) :
    ∃ j ∈ Finset.range (columnDyadicLength N + 1),
      (2 : ℝ)^j/2 < (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ (2 : ℝ)^j := by
  have hp : 1 ≤ Ideal.absNorm D := by exact_mod_cast hD
  exact exists_dyadic_shell (Ideal.absNorm D) (columnDyadicLength N) hp
    (hDN.trans (columnDyadicLength_cover N))

def divisorDyadicLabel (N : ℝ) (D : Ideal O) : Fin (columnDyadicLength N+1) :=
  if h : 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N then
    ⟨(positive_ideal_dyadic_exists N D h.1 h.2).choose,
      Finset.mem_range.mp (positive_ideal_dyadic_exists N D h.1 h.2).choose_spec.1⟩
  else ⟨0,by omega⟩

def divisorDyadicBin (S : Finset (Ideal O)) (N : ℝ)
    (j : Fin (columnDyadicLength N+1)) : Finset (Ideal O) :=
  S.filter (fun D => divisorDyadicLabel N D = j)

def divisorDyadicScale (j : ℕ) : ℝ := max 1 ((2 : ℝ)^j/2)

def columnDivisorPool {n : Type*} [Fintype n] (left : n → Ideal O) : Finset (Ideal O) :=
  Finset.univ.biUnion (fun j => IdealMobiusDivisorSum.idealDivisors (left j))

end CanonicalQuadraticSieve

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap

namespace EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT

def nonzeroLatticeEnvelopeConstant : ℝ :=
  4 * (1 + Real.pi) ^ 2 + 4 * eisensteinCauchyMass

end EisensteinSchwartzPoisson

namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def originalMiddleDecayConstant (W : 𝓢(ℝ, ℂ)) : ℝ :=
  (actual_middle_radial_block_bound.{0, 0, 0} W 2).choose

def dualMiddleDecayConstant (W : 𝓢(ℝ, ℂ)) : ℝ :=
  (actual_dual_middle_radial_block_bound.{0, 0, 0} W 2).choose

section
variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalMiddleAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (h : O) : ℝ :=
  ∑ D : S, ∑ E : T, ∑ i,
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖

def dualMiddleAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (h : O) : ℝ :=
  ∑ D : S, ∑ E : T, ∑ i,
    (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
        (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖

variable (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
  (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)

include hD₁ hD₂ hB hN hM hS hT hr hl hri hrows ha hb

end

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

end

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def divisorExponentConstant {α : ℝ} (h : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) : ℝ :=
  (h.divisor_pair deltaLoss hδ).choose

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
  (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
  (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
  (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)

include hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT hr hl hri hrows ha hb

end CanonicalQuadraticSieve

namespace CubicEisenstein
open Filter
open scoped BigOperators Classical Topology Matrix MatrixGroups

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def integralComplexMatrix : SL(2,O) →* SL(2,ℂ) := Matrix.SpecialLinearGroup.map eisEmbedding

@[simp] lemma integralComplexMatrix_apply (M : SL(2,O)) (i j : Fin 2) :
    integralComplexMatrix M i j = eisEmbedding (M i j) := rfl

lemma integralComplexMatrix_levelThree (M : levelThree) :
    integralComplexMatrix (M : SL(2,O)) = complexMatrix M := rfl

lemma row_wedge_gram (u v : Fin 2 → ℂ) :
    Complex.normSq (u 0*v 1-u 1*v 0) +
      Complex.normSq (u 0*star (v 0)+u 1*star (v 1)) = rowEnergy u * rowEnergy v := by
  simp only [rowEnergy,← Complex.normSq_eq_norm_sq,Complex.normSq_apply,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

lemma row_wedge_le_energy (u v : Fin 2 → ℂ) :
    Complex.normSq (u 0*v 1-u 1*v 0) ≤ rowEnergy u * rowEnergy v := by
  rw [← row_wedge_gram u v]
  exact le_add_of_nonneg_right (Complex.normSq_nonneg _)

lemma bottom_row_wedge_mul (g h : SL(2,ℂ)) :
    complexBottomRow (g*h) 0 * complexBottomRow h 1 -
      complexBottomRow (g*h) 1 * complexBottomRow h 0 = g 1 0 := by
  have hd : h 0 0*h 1 1-h 0 1*h 1 0=1 := by
    simpa only [Matrix.det_fin_two] using h.property
  simp only [complexBottomRow,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  linear_combination g 1 0 * hd

theorem hyperbolicHeight_mul_bound (g : SL(2,ℂ)) (w : HyperbolicSpace) :
    hyperbolicHeight (g • w) * hyperbolicHeight w * Complex.normSq (g 1 0) ≤ 1 := by
  induction w using Quotient.inductionOn with
  | _ h =>
    change liftedHeight (g*h) * liftedHeight h * Complex.normSq (g 1 0) ≤ 1
    have hw := row_wedge_le_energy (complexBottomRow (g*h)) (complexBottomRow h)
    rw [bottom_row_wedge_mul] at hw
    have hp : 0 < rowEnergy (complexBottomRow (g*h)) * rowEnergy (complexBottomRow h) :=
      mul_pos (rowEnergy_pos _ (complexBottomRow_ne_zero _))
        (rowEnergy_pos _ (complexBottomRow_ne_zero _))
    have he : liftedHeight (g*h) * liftedHeight h * Complex.normSq (g 1 0) =
        Complex.normSq (g 1 0) /
          (rowEnergy (complexBottomRow (g*h))*rowEnergy (complexBottomRow h)) := by
      simp only [liftedHeight,div_eq_mul_inv,mul_inv]
      ring
    rw [he]
    exact (div_le_one hp).mpr hw

lemma one_le_normSq_embedding (c : O) (hc : c≠0) : 1 ≤ Complex.normSq (eisEmbedding c) := by
  rw [Complex.normSq_eq_norm_sq,eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))

theorem integral_hyperbolicHeight_mul_le_one (M : SL(2,O)) (hc : M 1 0≠0) (w : HyperbolicSpace) :
    hyperbolicHeight (integralComplexMatrix M • w) * hyperbolicHeight w ≤ 1 := by
  have hb := hyperbolicHeight_mul_bound (integralComplexMatrix M) w
  have hc1 := one_le_normSq_embedding (M 1 0) hc
  have hp := mul_pos (hyperbolicHeight_pos (integralComplexMatrix M • w)) (hyperbolicHeight_pos w)
  change _ * _ * Complex.normSq (eisEmbedding (M 1 0)) ≤ 1 at hb
  nlinarith

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

lemma cosetHeight_pos (x : CuspCosets) (w : HyperbolicSpace) : 0<cosetHeight x w := by
  induction x using Quotient.inductionOn with
  | _ M => exact (cosetHeight_cosetOf M w).symm ▸ hyperbolicHeight_pos _

lemma cosetHeight_rightEquiv (M : levelThree) (x : CuspCosets) (w : HyperbolicSpace) :
    cosetHeight (rightEquiv M x) w = cosetHeight x (complexMatrix M • w) := by
  induction x using Quotient.inductionOn with
  | _ N =>
    change cosetHeight (cosetOf (N*M)) w = cosetHeight (cosetOf N) (complexMatrix M • w)
    rw [cosetHeight_cosetOf,cosetHeight_cosetOf,map_mul,mul_smul]

lemma high_coset_unique (Y : ℝ) (hY : 1≤Y) (w : HyperbolicSpace)
    (x y : CuspCosets) (hx : Y<cosetHeight x w) (hy : Y<cosetHeight y w) : x=y := by
  induction x using Quotient.inductionOn with | _ M =>
    induction y using Quotient.inductionOn with | _ N =>
      by_contra hne
      have hc : ((M*N⁻¹ : levelThree) : SL(2,O)) 1 0≠0 := by
        intro hc
        have hT : M*N⁻¹ ∈ cuspStabilizer := (mem_cuspStabilizer_iff _).mpr hc
        exact hne ((cosetOf_eq_iff M N).mpr ⟨M*N⁻¹,hT,by group⟩)
      have hp := integral_hyperbolicHeight_mul_le_one
        ((M*N⁻¹ : levelThree) : SL(2,O)) hc (complexMatrix N • w)
      rw [integralComplexMatrix_levelThree,map_mul,map_inv,mul_smul,inv_smul_smul] at hp
      change Y<cosetHeight (cosetOf M) w at hx
      change Y<cosetHeight (cosetOf N) w at hy
      rw [cosetHeight_cosetOf] at hx hy
      have hm := lt_of_le_of_lt hY hx
      have hn := lt_of_le_of_lt hY hy
      nlinarith [mul_pos (sub_pos.mpr hm) (sub_pos.mpr hn)]

lemma high_cosets_finite (Y : ℝ) (hY : 1≤Y) (w : HyperbolicSpace) :
    Set.Finite {x : CuspCosets | Y<cosetHeight x w} := by
  have h : Set.Subsingleton {x : CuspCosets | Y<cosetHeight x w} :=
    fun x hx y hy => high_coset_unique Y hY w x y hx hy
  exact h.finite

def cuspCutoffTerm (Y : ℝ) (F : ℝ → ℂ) (x : CuspCosets) (w : HyperbolicSpace) : ℂ :=
  if Y<cosetHeight x w then (cosetCharacter x)⁻¹ * F (cosetHeight x w) else 0

lemma cuspCutoffTerm_finiteSupport (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ) (w : HyperbolicSpace) :
    Function.HasFiniteSupport (fun x => cuspCutoffTerm Y F x w) := by
  apply (high_cosets_finite Y hY w).subset
  intro x hx
  by_contra hn
  simp only [Function.mem_support] at hx
  change ¬Y<cosetHeight x w at hn
  exact hx (by simp [cuspCutoffTerm,hn])

lemma cuspCutoffTerm_summable (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ) (w : HyperbolicSpace) :
    Summable (fun x => cuspCutoffTerm Y F x w) :=
  summable_of_hasFiniteSupport (cuspCutoffTerm_finiteSupport Y hY F w)

def cuspCutoffCorrection (Y : ℝ) (F : ℝ → ℂ) (w : HyperbolicSpace) : ℂ :=
  ∑'x,cuspCutoffTerm Y F x w

lemma cuspCutoffTerm_automorphy (Y : ℝ) (F : ℝ → ℂ) (M : levelThree)
    (x : CuspCosets) (w : HyperbolicSpace) :
    cuspCutoffTerm Y F x (complexMatrix M • w) =
      complexCharacter M * cuspCutoffTerm Y F (rightEquiv M x) w := by
  have hM : complexCharacter M≠0 := by
    intro h
    have hn := norm_complexCharacter M
    rw [h,norm_zero] at hn
    exact zero_ne_one hn
  simp only [cuspCutoffTerm,cosetHeight_rightEquiv,cosetCharacter_rightEquiv]
  split_ifs <;> simp [mul_inv_rev,hM,mul_assoc,mul_left_comm,mul_comm]

theorem cuspCutoffCorrection_automorphy (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ)
    (M : levelThree) (w : HyperbolicSpace) :
    cuspCutoffCorrection Y F (complexMatrix M • w) = complexCharacter M*cuspCutoffCorrection Y F w := by
  have hsum := cuspCutoffTerm_summable Y hY F w
  have hreindex := (rightEquiv M).hasSum_iff.mpr hsum.hasSum
  have hscale := hreindex.mul_left (complexCharacter M)
  exact (cuspCutoffTerm_summable Y hY F (complexMatrix M • w)).hasSum.unique
    (hscale.congr_fun (fun x => cuspCutoffTerm_automorphy Y F M x w))

lemma cuspCutoffCorrection_eq (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ)
    (w : HyperbolicSpace) (x : CuspCosets) (hx : Y<cosetHeight x w) :
    cuspCutoffCorrection Y F w = (cosetCharacter x)⁻¹*F (cosetHeight x w) := by
  unfold cuspCutoffCorrection
  rw [tsum_eq_single x]
  · simp [cuspCutoffTerm,hx]
  · intro y hy
    have hn : ¬Y<cosetHeight y w := fun hh => hy (high_coset_unique Y hY w y x hh hx)
    simp [cuspCutoffTerm,hn]

lemma hyperbolicHeight_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHeight (upperPoint z v hv)=v := by
  have h := hyperbolicHeight_action_upperPoint 1 z v hv
  simpa [Matrix.one_apply] using h

end CubicEisenstein

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def dualPrincipalKernel (W : 𝓢(ℝ, ℂ)) (rows : m → Ideal O)
    (left : n → Ideal O) (right : p → Ideal O) (M F : ℝ) (h : O)
    (d : Ideal O) (i : m) (j : n) (k : p) : ℂ :=
  ((Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
    paperRadialFourier W (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
      (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ))

def dualProductDivisorMiddleAt (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ i, ∑ d ∈ K, if P d i then
    ‖∑ j, ∑ k, if d ∣ left j * right k then
      originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d i j k else 0‖ else 0

end CanonicalQuadraticSieve

namespace DescentFiberCost
open ActualEisensteinCubic ConcreteTraceCRT
open ShortDraftLatticeCount ActualEisensteinCoordinates

theorem finite_element_count_real (S : Finset O) (K : ℝ) (hK : 1 ≤ K)
    (hS : ∀ z ∈ S, ‖eisEmbedding z‖^2 ≤ K) : (S.card : ℝ) ≤ 128*K := by
  have hbound : ∀ z ∈ S, q (coords z) ≤ (⌊K⌋₊ : ℕ) := by
    intro z hz
    have hq : (qNat z : ℝ) ≤ K := by
      rw [qNat_eq_absNorm_span, ← eisEmbedding_norm_sq_eq_absNorm_span]
      exact hS z hz
    have hn := Nat.le_floor hq
    have he : (qNat z : ℤ) = q (coords z) := Int.toNat_of_nonneg (qO_nonneg z)
    rw [← he]
    exact_mod_cast hn
  have hcard := actual_eisenstein_count S ⌊K⌋₊ hbound
  have hr : (S.card : ℝ) ≤ 64*((⌊K⌋₊ : ℝ)+1) := by exact_mod_cast hcard
  have hf : (⌊K⌋₊ : ℝ) ≤ K := Nat.floor_le (by linarith)
  linarith

end DescentFiberCost

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma axisSlice_update (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) :
    axisSlice f (Function.update p j t) j = axisSlice f p j := by
  funext z
  simp only [axisSlice,Function.update_idem]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

@[fun_prop] lemma quadraticHeightDenominator_continuous (A B C D : ℝ) :
    Continuous (fun p : SpatialCoordinates => quadraticHeightDenominator A B C D (p 0) (p 1) (p 2)) := by
  unfold quadraticHeightDenominator
  fun_prop

def smoothFirstCoefficient (s : ℂ) (r : CuspCosets) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  smoothSummand s r p*s*(rowLogD (embeddedRow r) p j:ℂ)
def smoothSecondCoefficient (s : ℂ) (r : CuspCosets) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  smoothSummand s r p*(s^2*(rowLogD (embeddedRow r) p j:ℂ)^2+s*(rowLogDD (embeddedRow r) p j:ℂ))

lemma smoothFirstCoefficient_eq_deriv (s : ℂ) (r : CuspCosets) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothFirstCoefficient s r j p=deriv (axisSlice (smoothSummand s r) p j) (p j) := by
  unfold axisSlice smoothSummand
  rw [deriv_const_mul_field]
  have hd := (row_axis_hasDerivAt s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).deriv
  unfold axisSlice at hd
  rw [hd]
  unfold smoothFirstCoefficient smoothSummand
  ring

lemma smoothSecondCoefficient_eq_deriv (s : ℂ) (r : CuspCosets) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothSecondCoefficient s r j p=deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j) := by
  unfold axisSlice smoothSummand
  rw [deriv_const_mul_field',deriv_const_mul_field]
  have hd := (row_axis_hasDerivAt_deriv s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).deriv
  unfold axisSlice at hd
  rw [hd]
  unfold smoothSecondCoefficient smoothSummand
  ring

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma spatial_summable_derivative_bounds (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    ∃ U : Set SpatialCoordinates, IsOpen U ∧ p∈U ∧
      ∃ M₀ M₁ M₂ : CuspCosets → ℝ,
      Summable M₀ ∧ Summable M₁ ∧ Summable M₂ ∧
      ∀q∈U, 0<q 2 ∧ ∀r : CuspCosets,
        ‖smoothSummand s r q‖≤M₀ r ∧ ∀j : Fin 3,
        ‖smoothFirstCoefficient s r j q‖≤M₁ r ∧
        ‖smoothSecondCoefficient s r j q‖≤M₂ r := by
  let deltaLoss : ℝ := p 2/2
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let path := clampedCoordinates deltaLoss hδ
  let C := rowBound (coordinateSection (path p))+1
  have hC : 0<C := by dsimp [C]; linarith [rowBound_pos (coordinateSection (path p))]
  let U : Set SpatialCoordinates := {q | deltaLoss<q 2 ∧ rowBound (coordinateSection (path q))<C}
  have hU : IsOpen U := (isOpen_lt continuous_const (continuous_apply 2)).inter
    (isOpen_lt (continuous_coordinate_rowBound.comp (continuous_clampedCoordinates deltaLoss hδ)) continuous_const)
  have hpU : p∈U := by constructor <;> dsimp [deltaLoss,C] <;> linarith
  obtain ⟨M,hM,hMnonneg,hbound⟩ := coordinate_summable_majorant C s.re s.re hC hs hs
  let c₁ := ‖s‖*(1/deltaLoss)
  let c₂ := ‖s‖^2*(1/deltaLoss)^2 + ‖s‖*(7/deltaLoss^2)
  refine ⟨U,hU,hpU,M,fun r => M r*c₁,fun r => M r*c₂,hM,hM.mul_right _,hM.mul_right _,?_⟩
  intro q hq
  have hpos : 0<q 2 := lt_trans hδ hq.1
  refine ⟨hpos,fun r => ?_⟩
  have hm : ‖smoothSummand s r q‖≤M r := by
    rw [smoothSummand_eq_clamped s r q deltaLoss hδ hq.1.le]
    exact hbound (path q,s) hq.2.le le_rfl le_rfl r
  have hfrac : 1 / q 2 ≤ 1/deltaLoss := one_div_le_one_div_of_le hδ hq.1.le
  have hfrac₂ : 7 / (q 2)^2 ≤ 7/deltaLoss^2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ)
    nlinarith [hq.1]
  refine ⟨hm,fun j => ?_⟩
  rw [smoothFirstCoefficient_eq_deriv _ _ _ _ hpos,smoothSecondCoefficient_eq_deriv _ _ _ _ hpos]
  constructor
  · apply (norm_smooth_axis_deriv s r q hpos j).trans
    apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    exact mul_le_mul_of_nonneg_left hfrac (norm_nonneg s)
  · apply (norm_smooth_axis_deriv2 s r q hpos j).trans
    apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    dsimp [c₂]
    gcongr

end CubicEisenstein

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

def cuspTransition (a b v : ℝ) : ℝ := Real.smoothTransition ((v-a)/(b-a))

lemma cuspTransition_contDiff (a b : ℝ) : ContDiff ℝ ∞ (cuspTransition a b) := by
  unfold cuspTransition
  fun_prop

lemma cuspTransition_zero (a b v : ℝ) (hab : a<b) (hv : v≤a) : cuspTransition a b v=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv) (sub_pos.mpr hab).le)
lemma cuspTransition_one (a b v : ℝ) (hab : a<b) (hv : b≤v) : cuspTransition a b v=1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hab)).mpr (by linarith))

lemma cuspTransition_derivatives (a b v : ℝ) (hab : a<b) (hv : v<a ∨ b<v) :
    deriv (cuspTransition a b) v=0 ∧ deriv (deriv (cuspTransition a b)) v=0 := by
  rcases hv with hv | hv
  · have heq : cuspTransition a b =ᶠ[𝓝 v] (fun _ => (0:ℝ)) := by
      filter_upwards [Iio_mem_nhds hv] with x hx
      exact cuspTransition_zero a b x hab hx.le
    exact ⟨heq.deriv_eq.trans (deriv_const _ _),heq.deriv.deriv_eq.trans (by simp)⟩
  · have heq : cuspTransition a b =ᶠ[𝓝 v] (fun _ => (1:ℝ)) := by
      filter_upwards [Ioi_mem_nhds hv] with x hx
      exact cuspTransition_one a b x hab hx.le
    exact ⟨heq.deriv_eq.trans (deriv_const _ _),heq.deriv.deriv_eq.trans (by simp)⟩

def positiveHeightPower (s : ℂ) (v : ℝ) : ℂ := logRatioPower s v 1
lemma positiveHeightPower_eq_cpow (s : ℂ) (v : ℝ) (hv : 0<v) :
    positiveHeightPower s v=(v:ℂ)^s := by
  simpa only [positiveHeightPower,div_one] using logRatioPower_eq_cpow s hv (by norm_num : (0:ℝ)<1)

lemma positiveHeightPower_hasDerivAt (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (positiveHeightPower s) (positiveHeightPower s v*s/(v:ℂ)) v := by
  convert (preTransparency := .instances) hasDerivAt_logRatioPower s (hasDerivAt_id v) (hasDerivAt_const v (1:ℝ)) hv one_ne_zero using 1
  · rfl
  · simp [positiveHeightPower,div_eq_mul_inv]

lemma positiveHeightPower_hasDerivAt_deriv (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (deriv (positiveHeightPower s))
      (positiveHeightPower s v*s*(s-1)/(v:ℂ)^2) v := by
  convert (preTransparency := .instances) hasDerivAt_deriv_logRatioPower s id (fun _ => 1) (fun _ => 1) (fun _ => 0) v 0 0
    (fun x => hasDerivAt_id x) (fun x => hasDerivAt_const x (1:ℝ))
    (hasDerivAt_const v (1:ℝ)) (hasDerivAt_const v (0:ℝ)) hv one_ne_zero using 1
  · rfl
  · simp only [id_eq,zero_mul,mul_one,sub_self,sub_zero,one_pow,div_one,
      Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_pow,
      Complex.ofReal_zero,positiveHeightPower]
    field_simp [Complex.ofReal_ne_zero.mpr hv]
    ; ring

def cuspSeedProfile (a b : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  (cuspTransition a b v:ℂ)*positiveHeightPower s v

lemma cuspSeedProfile_zero (a b : ℝ) (s : ℂ) (v : ℝ) (hab : a<b) (hv : v≤a) :
    cuspSeedProfile a b s v=0 := by simp [cuspSeedProfile,cuspTransition_zero a b v hab hv]
lemma cuspSeedProfile_incoming (a b : ℝ) (s : ℂ) (v : ℝ)
    (hab : a<b) (hv : b≤v) (hpos : 0<v) : cuspSeedProfile a b s v=(v:ℂ)^s := by
  simp [cuspSeedProfile,cuspTransition_one a b v hab hv,positiveHeightPower_eq_cpow s v hpos]

lemma cuspSeedProfile_hasDerivAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (cuspSeedProfile a b s)
      (((deriv (cuspTransition a b) v:ℝ):ℂ)*positiveHeightPower s v+
        (cuspTransition a b v:ℂ)*(positiveHeightPower s v*s/(v:ℂ))) v := by
  exact (((cuspTransition_contDiff a b).differentiable (by simp) v).hasDerivAt.ofReal_comp).mul
    (positiveHeightPower_hasDerivAt s v hv)

lemma cuspSeedProfile_hasDerivAt_deriv (a b : ℝ) (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (deriv (cuspSeedProfile a b s))
      (((deriv (deriv (cuspTransition a b)) v:ℝ):ℂ)*positiveHeightPower s v+
        2*((deriv (cuspTransition a b) v:ℝ):ℂ)*(positiveHeightPower s v*s/(v:ℂ))+
        (cuspTransition a b v:ℂ)*(positiveHeightPower s v*s*(s-1)/(v:ℂ)^2)) v := by
  have hχ := ((cuspTransition_contDiff a b).differentiable (by simp) v).hasDerivAt.ofReal_comp
  have hdχ := (((contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2).differentiable
    (by simp) v).hasDerivAt.ofReal_comp
  have hH := positiveHeightPower_hasDerivAt s v hv
  have hdH := positiveHeightPower_hasDerivAt_deriv s v hv
  have heq : deriv (cuspSeedProfile a b s) =ᶠ[𝓝 v]
      (fun x => ((deriv (cuspTransition a b) x:ℝ):ℂ)*positiveHeightPower s x+
        (cuspTransition a b x:ℂ)*deriv (positiveHeightPower s) x) := by
    filter_upwards [eventually_ne_nhds hv] with x hx
    rw [(cuspSeedProfile_hasDerivAt a b s x hx).deriv,(positiveHeightPower_hasDerivAt s x hx).deriv]
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert (preTransparency := .instances) (hdχ.mul hH).add (hχ.mul hdH) using 1
  · rw [hH.deriv]
    ring

def cuspSeedDefectProfile (a b : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  positiveHeightPower s v*((v:ℂ)^2*((deriv (deriv (cuspTransition a b)) v:ℝ):ℂ)+
    (2*s-1)*(v:ℂ)*((deriv (cuspTransition a b) v:ℝ):ℂ))

lemma cuspSeedProfile_laplace_defect (a b : ℝ) (s : ℂ) (v : ℝ) (hv : v≠0) :
    (v:ℂ)^2*deriv (deriv (cuspSeedProfile a b s)) v-
      (v:ℂ)*deriv (cuspSeedProfile a b s) v-s*(s-2)*cuspSeedProfile a b s v=
        cuspSeedDefectProfile a b s v := by
  rw [(cuspSeedProfile_hasDerivAt a b s v hv).deriv,(cuspSeedProfile_hasDerivAt_deriv a b s v hv).deriv]
  unfold cuspSeedDefectProfile cuspSeedProfile
  field_simp [Complex.ofReal_ne_zero.mpr hv]
  ; ring

lemma cuspSeedDefectProfile_zero (a b : ℝ) (s : ℂ) (v : ℝ) (hab : a<b) (hv : v<a ∨ b<v) :
    cuspSeedDefectProfile a b s v=0 := by
  obtain ⟨h₁,h₂⟩ := cuspTransition_derivatives a b v hab hv
  simp [cuspSeedDefectProfile,h₁,h₂]

lemma cuspSeedDefectProfile_hasCompactSupport (a b : ℝ) (s : ℂ) (hab : a<b) :
    HasCompactSupport (cuspSeedDefectProfile a b s) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro v hv
  by_contra hn
  have hout : v<a ∨ b<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hn
  exact hv (cuspSeedDefectProfile_zero a b s v hab hout)

def rowHeight (u : Fin 2 → ℂ) (p : SpatialCoordinates) : ℝ :=
  p 2 / quadraticHeightDenominator (Complex.normSq (u 0)) (u 0*star (u 1)).re
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2)

lemma rowHeight_pos (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    0< rowHeight u p := div_pos hp (row_denominator_pos u hu p hp)
lemma rowHeight_eq_transformedHeight (u : Fin 2 → ℂ) (p : SpatialCoordinates) :
    rowHeight u p=transformedHeight ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) u := by
  rw [transformedHeight,heightDenominator_eq_quadratic]
  rfl
lemma cosetHeight_upperPoint_rowHeight (r : CuspCosets) (p : SpatialCoordinates) (hp : 0<p 2) :
    cosetHeight r (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)=rowHeight (embeddedRow r) p := by
  change (rowEnergy (rowOperator (upperSection ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) (embeddedRow r)))⁻¹=_
  rw [rowEnergy_upperSection,inv_div,heightDenominator_eq_quadratic]
  rfl

lemma rowHeight_contDiffAt (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (rowHeight u) p := by
  have hq : ContDiffAt ℝ ∞
      (fun q : SpatialCoordinates => quadraticHeightDenominator (Complex.normSq (u 0))
        (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (q 0) (q 1) (q 2)) p := by
    unfold quadraticHeightDenominator
    fun_prop
  exact (show ContDiffAt ℝ ∞ (fun q : SpatialCoordinates => q 2) p by fun_prop).div hq
    (row_denominator_pos u hu p hp).ne'

lemma rowSmoothPower_eq_height (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) : rowSmoothPower s u p=(rowHeight u p:ℂ)^s :=
  logRatioPower_eq_cpow s hp (row_denominator_pos u hu p hp)

lemma norm_smoothSummand_three (r : CuspCosets) (p : SpatialCoordinates) (hp : 0<p 2) :
    ‖smoothSummand 3 r p‖=(rowHeight (embeddedRow r) p)^3 := by
  rw [smoothSummand,rowSmoothPower_eq_height 3 _ (embeddedRow_ne_zero r) p hp,norm_mul,norm_inv,
    norm_cosetCharacter,inv_one,one_mul]
  rw [show (3:ℂ)=(3:ℕ) by norm_num,Complex.cpow_natCast,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (rowHeight_pos _ (embeddedRow_ne_zero r) p hp)]

lemma locally_finite_high_rows (p : SpatialCoordinates) (hp : 0<p 2) :
    ∃U : Set SpatialCoordinates, IsOpen U ∧ p∈U ∧ ∃S : Finset CuspCosets,
      ∀q∈U, 0<q 2 ∧ ∀r∉S,rowHeight (embeddedRow r) q<1 := by
  obtain ⟨U,hU,hpU,M₀,M₁,M₂,hM₀,hM₁,hM₂,hbound⟩ :=
    spatial_summable_derivative_bounds 3 (by norm_num) p hp
  have hevent : ∀ᶠr in Filter.cofinite,M₀ r<1 :=
    hM₀.tendsto_cofinite_zero.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  have hfinite : Set.Finite {r | ¬M₀ r<1} := Filter.eventually_cofinite.mp hevent
  refine ⟨U,hU,hpU,hfinite.toFinset,?_⟩
  intro q hq
  refine ⟨(hbound q hq).1,?_⟩
  intro r hr
  have hrM : M₀ r<1 := by simpa only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq,not_not] using hr
  have hnorm := ((hbound q hq).2 r).1
  rw [norm_smoothSummand_three r q (hbound q hq).1] at hnorm
  have hpos := (rowHeight_pos _ (embeddedRow_ne_zero r) q (hbound q hq).1).le
  nlinarith [sq_nonneg (rowHeight (embeddedRow r) q-1)]

def heightPoincareField (F : ℝ → ℂ) (p : SpatialCoordinates) : ℂ :=
  ∑'r : CuspCosets,(cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) p)

lemma heightPoincareField_locally_finite (F : ℝ → ℂ) (hF : ∀v≤1,F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ∃S : Finset CuspCosets, heightPoincareField F =ᶠ[𝓝 p]
      (fun q => ∑r∈S,(cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) q)) := by
  obtain ⟨U,hU,hpU,S,hrows⟩ := locally_finite_high_rows p hp
  refine ⟨S,?_⟩
  filter_upwards [hU.mem_nhds hpU] with q hq
  apply tsum_eq_sum
  intro r hr
  rw [hF _ ((hrows q hq).2 r hr).le,mul_zero]

lemma heightPoincareField_contDiffAt (F : ℝ → ℂ) (hzero : ∀v≤1,F v=0)
    (hF : ∀v,0<v→ ContDiffAt ℝ ∞ F v) (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (heightPoincareField F) p := by
  obtain ⟨S,hS⟩ := heightPoincareField_locally_finite F hzero p hp
  apply ContDiffAt.congr_of_eventuallyEq _ hS
  apply ContDiffAt.sum
  intro r hr
  exact contDiffAt_const.mul ((hF _ (rowHeight_pos _ (embeddedRow_ne_zero r) p hp)).comp p
    (rowHeight_contDiffAt _ (embeddedRow_ne_zero r) p hp))

lemma heightPoincareField_eq_cuspCorrection (F : ℝ → ℂ) (hzero : ∀v≤1,F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    heightPoincareField F p=cuspCutoffCorrection 1 F
      (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) := by
  unfold heightPoincareField cuspCutoffCorrection
  apply tsum_congr
  intro r
  rw [cuspCutoffTerm,cosetHeight_upperPoint_rowHeight]
  split_ifs with h
  · rfl
  · rw [hzero _ (le_of_not_gt h),mul_zero]

open CubicKubota

lemma positiveHeightPower_contDiffAt (s : ℂ) (v : ℝ) (hv : v≠0) :
    ContDiffAt ℝ ∞ (positiveHeightPower s) v := by
  have hlog : ContDiffAt ℝ ∞ (fun x : ℝ => (Real.log x:ℂ)) v :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp v (Real.contDiffAt_log.mpr hv)
  have hs : ContDiffAt ℝ ∞ (fun x : ℝ => s*(Real.log x:ℂ)) v := contDiffAt_const.mul hlog
  unfold positiveHeightPower logRatioPower
  simpa only [Real.log_one,sub_zero] using hs.cexp

lemma cuspSeedProfile_contDiffAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ContDiffAt ℝ ∞ (cuspSeedProfile a b s) v :=
  (Complex.ofRealCLM.contDiff.contDiffAt.comp v (cuspTransition_contDiff a b).contDiffAt).mul
    (positiveHeightPower_contDiffAt s v hv.ne')

lemma cuspSeedDefectProfile_contDiffAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ContDiffAt ℝ ∞ (cuspSeedDefectProfile a b s) v := by
  have hχ₁ : ContDiff ℝ ∞ (deriv (cuspTransition a b)) :=
    (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2
  have hχ₂ : ContDiff ℝ ∞ (deriv (deriv (cuspTransition a b))) :=
    (contDiff_infty_iff_deriv.mp hχ₁).2
  have hd₁ := Complex.ofRealCLM.contDiff.contDiffAt.comp v hχ₁.contDiffAt
  have hd₂ := Complex.ofRealCLM.contDiff.contDiffAt.comp v hχ₂.contDiffAt
  have hid : ContDiffAt ℝ ∞ (fun x : ℝ => (x:ℂ)) v := Complex.ofRealCLM.contDiff.contDiffAt
  exact (positiveHeightPower_contDiffAt s v hv.ne').mul
    (((hid.pow 2).mul hd₂).add ((contDiffAt_const.mul hid).mul hd₁))

lemma cuspSeedDefectProfile_continuous (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Continuous (cuspSeedDefectProfile a b s) := by
  rw [continuous_iff_continuousAt]
  intro v
  by_cases hv : v<a
  · have heq : cuspSeedDefectProfile a b s =ᶠ[𝓝 v] (fun _ => (0:ℂ)) := by
      filter_upwards [Iio_mem_nhds hv] with x hx
      exact cuspSeedDefectProfile_zero a b s x hab (Or.inl hx)
    exact continuousAt_const.congr heq.symm
  · exact (cuspSeedDefectProfile_contDiffAt a b s v (lt_of_lt_of_le ha (le_of_not_gt hv))).continuousAt

def smoothCuspSeed (a b : ℝ) (s : ℂ) : HyperbolicSpace → ℂ :=
  cuspCutoffCorrection 1 (cuspSeedProfile a b s)

def smoothCuspSeedDefect (a b : ℝ) (s : ℂ) : HyperbolicSpace → ℂ :=
  cuspCutoffCorrection 1 (cuspSeedDefectProfile a b s)

lemma smoothCuspSeed_automorphy (a b : ℝ) (s : ℂ) (M : levelThree) (w : HyperbolicSpace) :
    smoothCuspSeed a b s (complexMatrix M • w)=complexCharacter M*smoothCuspSeed a b s w :=
  cuspCutoffCorrection_automorphy 1 le_rfl _ M w
lemma smoothCuspSeedDefect_automorphy (a b : ℝ) (s : ℂ) (M : levelThree) (w : HyperbolicSpace) :
    smoothCuspSeedDefect a b s (complexMatrix M • w)=complexCharacter M*smoothCuspSeedDefect a b s w :=
  cuspCutoffCorrection_automorphy 1 le_rfl _ M w

lemma smoothCuspSeed_coordinate (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeed a b s (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)=
      heightPoincareField (cuspSeedProfile a b s) p :=
  (heightPoincareField_eq_cuspCorrection _
    (fun v hv => cuspSeedProfile_zero a b s v hab (hv.trans ha.le)) p hp).symm
lemma smoothCuspSeedDefect_coordinate (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeedDefect a b s (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)=
      heightPoincareField (cuspSeedDefectProfile a b s) p :=
  (heightPoincareField_eq_cuspCorrection _
    (fun v hv => cuspSeedDefectProfile_zero a b s v hab (Or.inl (lt_of_le_of_lt hv ha))) p hp).symm

lemma smoothCuspSeed_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (heightPoincareField (cuspSeedProfile a b s)) p :=
  heightPoincareField_contDiffAt _ (fun v hv => cuspSeedProfile_zero a b s v hab (hv.trans ha.le))
    (cuspSeedProfile_contDiffAt a b s) p hp

lemma smoothCuspSeedDefect_support (a b : ℝ) (s : ℂ) (hab : a<b) (w : HyperbolicSpace)
    (hw : smoothCuspSeedDefect a b s w≠0) :
    ∃r : CuspCosets, a≤ cosetHeight r w ∧ cosetHeight r w≤b := by
  by_contra hn
  apply hw
  unfold smoothCuspSeedDefect cuspCutoffCorrection
  calc
    _ = ∑'r : CuspCosets, (0:ℂ) := by
      apply tsum_congr
      intro r
      have hout : cosetHeight r w<a ∨ b<cosetHeight r w := by
        have h := not_exists.mp hn r
        simpa only [not_and_or,not_le] using h
      simp [cuspCutoffTerm,cuspSeedDefectProfile_zero a b s _ hab hout]
    _ = 0 := tsum_zero

end

open Filter
open scoped BigOperators Classical Topology ContDiff

def rowLogHeight (u : Fin 2 → ℂ) (p : SpatialCoordinates) : ℝ :=
  Real.log (p 2)-Real.log (quadraticHeightDenominator (Complex.normSq (u 0))
    (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2))

lemma exp_rowLogHeight (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    Real.exp (rowLogHeight u p)=rowHeight u p := by
  rw [rowLogHeight,Real.exp_sub,Real.exp_log hp,Real.exp_log (row_denominator_pos u hu p hp)]
  rfl

lemma hasDerivAt_deriv_log_ratio (f g df dg : ℝ → ℝ) (x ddf ddg : ℝ)
    (hf : ∀t,HasDerivAt f (df t) t) (hg : ∀t,HasDerivAt g (dg t) t)
    (hdf : HasDerivAt df ddf x) (hdg : HasDerivAt dg ddg x)
    (hf0 : f x≠0) (hg0 : g x≠0) :
    HasDerivAt (deriv (fun t => Real.log (f t)-Real.log (g t)))
      ((ddf*f x-df x*df x)/(f x)^2-(ddg*g x-dg x*dg x)/(g x)^2) x := by
  have heq : deriv (fun t => Real.log (f t)-Real.log (g t)) =ᶠ[𝓝 x]
      (fun t => df t/f t-dg t/g t) := by
    filter_upwards [((hf x).continuousAt.eventually_ne hf0).and ((hg x).continuousAt.eventually_ne hg0)] with t ht
    exact (((hf t).log ht.1).sub ((hg t).log ht.2)).deriv
  exact ((hdf.div (hf x) hf0).sub (hdg.div (hg x) hg0)).congr_of_eventuallyEq heq

lemma rowLogHeight_hasDerivAt (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    HasDerivAt (fun t => rowLogHeight u (Function.update p j t)) (rowLogD u p j) (p j) := by
  let A := Complex.normSq (u 0)
  let B := (u 0*star (u 1)).re
  let C := -(u 0*star (u 1)).im
  let D := Complex.normSq (u 1)
  have hq := (row_denominator_pos u hu p hp).ne'
  fin_cases j
  · have h := ((hasDerivAt_const (p 0) (p 2)).log hp.ne').sub
      ((quadraticHeightDenominator_hasDerivAt_x A B C D (p 0) (p 1) (p 2)).log hq)
    simpa [rowLogHeight,rowLogD,spatialLogD,heightLogDx,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := ((hasDerivAt_const (p 1) (p 2)).log hp.ne').sub
      ((quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) (p 1) (p 2)).log hq)
    simpa [rowLogHeight,rowLogD,spatialLogD,heightLogDy,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := ((hasDerivAt_id (p 2)).log hp.ne').sub
      ((quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) (p 2)).log hq)
    simpa [rowLogHeight,rowLogD,spatialLogD,heightLogDv,Function.update,A,B,C,D,Pi.sub_def] using! h

lemma rowLogHeight_hasDerivAt_deriv (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    HasDerivAt (deriv (fun t => rowLogHeight u (Function.update p j t))) (rowLogDD u p j) (p j) := by
  let A := Complex.normSq (u 0)
  let B := (u 0*star (u 1)).re
  let C := -(u 0*star (u 1)).im
  let D := Complex.normSq (u 1)
  have hq := (row_denominator_pos u hu p hp).ne'
  fin_cases j
  · have h := hasDerivAt_deriv_log_ratio (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D t (p 1) (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+B)) (p 0) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_x A B C D t (p 1) (p 2))
      (hasDerivAt_const (p 0) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 0)).const_mul A |>.add_const B).const_mul 2)
      hp.ne' hq
    simpa [rowLogHeight,rowLogDD,spatialLogDD,heightLogDxx,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := hasDerivAt_deriv_log_ratio (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D (p 0) t (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+C)) (p 1) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) t (p 2))
      (hasDerivAt_const (p 1) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 1)).const_mul A |>.add_const C).const_mul 2)
      hp.ne' hq
    simpa [rowLogHeight,rowLogDD,spatialLogDD,heightLogDyy,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := hasDerivAt_deriv_log_ratio id
      (fun t => quadraticHeightDenominator A B C D (p 0) (p 1) t) (fun _ => 1)
      (fun t => 2*A*t) (p 2) 0 (2*A)
      (fun t => hasDerivAt_id t)
      (fun t => quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) t)
      (hasDerivAt_const (p 2) 1)
      (by simpa only [id_eq,mul_one] using (hasDerivAt_id (p 2)).const_mul (2*A))
      hp.ne' hq
    simpa [rowLogHeight,rowLogDD,spatialLogDD,heightLogDvv,Function.update,A,B,C,D,div_eq_mul_inv] using h

lemma complex_profile_second_chain (F : ℝ → ℂ) (g : ℝ → ℝ) (x dg ddg : ℝ) (dF ddF : ℂ)
    (hg : HasDerivAt g dg x) (hdg : HasDerivAt (deriv g) ddg x)
    (hF : HasDerivAt F dF (g x)) (hdF : HasDerivAt (deriv F) ddF (g x))
    (hlocal : ∀ᶠy in 𝓝 x,DifferentiableAt ℝ g y ∧ DifferentiableAt ℝ F (g y)) :
    HasDerivAt (deriv (fun y => F (g y))) (ddF*(dg:ℂ)^2+dF*(ddg:ℂ)) x := by
  have heq : deriv (fun y => F (g y)) =ᶠ[𝓝 x]
      (fun y => (deriv g y:ℝ) • deriv F (g y)) := by
    filter_upwards [hlocal] with y hy
    exact (hy.2.hasDerivAt.scomp y hy.1.hasDerivAt).deriv
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert (preTransparency := .instances) hdg.smul (hdF.scomp x hg) using 1
  · rfl
  · simp only [Function.comp_apply,hg.deriv,hF.deriv,Complex.real_smul]
    ring

lemma positiveProfile_differentiable (F : ℝ → ℂ)
    (hF : ∀v,0<v→ ContDiffAt ℝ ∞ F v) (v : ℝ) (hv : 0<v) :
    DifferentiableAt ℝ F v ∧ DifferentiableAt ℝ (deriv F) v :=
  ⟨(hF v hv).differentiableAt (by simp),
    ((hF v hv).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)⟩

lemma positiveProfile_exp_derivatives (F : ℝ → ℂ)
    (hF : ∀v,0<v→ ContDiffAt ℝ ∞ F v) (t : ℝ) :
    HasDerivAt (fun y => F (Real.exp y))
      (deriv F (Real.exp t)*(Real.exp t:ℂ)) t ∧
    HasDerivAt (deriv (fun y => F (Real.exp y)))
      (deriv (deriv F) (Real.exp t)*(Real.exp t:ℂ)^2+
        deriv F (Real.exp t)*(Real.exp t:ℂ)) t := by
  have hdf := positiveProfile_differentiable F hF (Real.exp t) (Real.exp_pos t)
  constructor
  · simpa only [Complex.real_smul,mul_comm,Function.comp_def] using! hdf.1.hasDerivAt.scomp t (Real.hasDerivAt_exp t)
  · apply complex_profile_second_chain F Real.exp t (Real.exp t) (Real.exp t)
      (deriv F (Real.exp t)) (deriv (deriv F) (Real.exp t)) (Real.hasDerivAt_exp t)
      (by simpa only [Real.deriv_exp] using Real.hasDerivAt_exp t) hdf.1.hasDerivAt hdf.2.hasDerivAt
    exact Filter.Eventually.of_forall (fun y =>
      ⟨Real.differentiable_exp y,(positiveProfile_differentiable F hF _ (Real.exp_pos y)).1⟩)

lemma rowProfile_axis_derivatives (F : ℝ → ℂ)
    (hF : ∀v,0<v→ ContDiffAt ℝ ∞ F v) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    HasDerivAt (axisSlice (fun q => F (rowHeight u q)) p j)
      (deriv F (rowHeight u p)*(rowHeight u p:ℂ)*(rowLogD u p j:ℂ)) (p j) ∧
    HasDerivAt (deriv (axisSlice (fun q => F (rowHeight u q)) p j))
      (deriv (deriv F) (rowHeight u p)*(rowHeight u p:ℂ)^2*(rowLogD u p j:ℂ)^2+
       deriv F (rowHeight u p)*(rowHeight u p:ℂ)*
        ((rowLogD u p j:ℂ)^2+(rowLogDD u p j:ℂ))) (p j) := by
  let g : ℝ → ℝ := fun t => rowLogHeight u (Function.update p j t)
  let G : ℝ → ℂ := fun t => F (Real.exp t)
  have hg : HasDerivAt g (rowLogD u p j) (p j) := rowLogHeight_hasDerivAt u hu p hp j
  have hdg : HasDerivAt (deriv g) (rowLogDD u p j) (p j) := rowLogHeight_hasDerivAt_deriv u hu p hp j
  have hgval : g (p j)=rowLogHeight u p := by simp [g,Function.update_eq_self]
  have hexp : Real.exp (g (p j))=rowHeight u p := by rw [hgval,exp_rowLogHeight u hu p hp]
  have hG := positiveProfile_exp_derivatives F hF (g (p j))
  have hnear : ∀ᶠt in 𝓝 (p j),0<(Function.update p j t) 2 :=
    ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
      (by simpa only [Function.comp_apply,Function.update_eq_self] using hp)
  have heq : axisSlice (fun q => F (rowHeight u q)) p j =ᶠ[𝓝 (p j)] (fun t => G (g t)) := by
    filter_upwards [hnear] with t ht
    change F (rowHeight u (Function.update p j t))=F (Real.exp (rowLogHeight u (Function.update p j t)))
    rw [exp_rowLogHeight u hu _ ht]
  constructor
  · have hh := hG.1.scomp (p j) hg
    apply HasDerivAt.congr_of_eventuallyEq _ heq
    convert (preTransparency := .instances) hh using 1
    · rfl
    · simp only [Complex.real_smul,hexp]
      ring
  · have hlocal : ∀ᶠy in 𝓝 (p j),DifferentiableAt ℝ g y ∧ DifferentiableAt ℝ G (g y) := by
      filter_upwards [hnear] with y hy
      constructor
      · have h := rowLogHeight_hasDerivAt u hu (Function.update p j y) hy j
        simpa only [Function.update_idem,Function.update_self] using h.differentiableAt
      · exact (positiveProfile_exp_derivatives F hF (g y)).1.differentiableAt
    have hh := complex_profile_second_chain G g (p j) (rowLogD u p j) (rowLogDD u p j)
      _ _ hg hdg hG.1 hG.2 hlocal
    apply HasDerivAt.congr_of_eventuallyEq _ heq.deriv
    convert (preTransparency := .instances) hh using 1
    · rw [hexp]
      ring

lemma rowLog_eikonal (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    (p 2)^2*((rowLogD u p 0)^2+(rowLogD u p 1)^2+(rowLogD u p 2)^2)=1 := by
  exact heightLog_eikonal _ _ _ _ _ _ _ (complex_row_quadratic_relation (u 0) (u 1)) hp.ne'
    (row_denominator_pos u hu p hp).ne'
lemma rowLog_laplacian (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    (p 2)^2*(rowLogDD u p 0+rowLogDD u p 1+rowLogDD u p 2)-(p 2)*rowLogD u p 2= -2 := by
  exact heightLog_laplacian _ _ _ _ _ _ _ (complex_row_quadratic_relation (u 0) (u 1)) hp.ne'
    (row_denominator_pos u hu p hp).ne'

theorem rowProfile_laplacian (F : ℝ → ℂ) (hF : ∀v,0<v→ ContDiffAt ℝ ∞ F v)
    (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => F (rowHeight u q)) p=
      (rowHeight u p:ℂ)^2*deriv (deriv F) (rowHeight u p)-(rowHeight u p:ℂ)*deriv F (rowHeight u p) := by
  have hp0 := rowProfile_axis_derivatives F hF u hu p hp 0
  have hp1 := rowProfile_axis_derivatives F hF u hu p hp 1
  have hp2 := rowProfile_axis_derivatives F hF u hu p hp 2
  unfold axisLaplacian
  rw [Fin.sum_univ_three,hp0.2.deriv,hp1.2.deriv,hp2.2.deriv,hp2.1.deriv]
  have hE := congrArg (fun r : ℝ => (r:ℂ)) (rowLog_eikonal u hu p hp)
  have hD := congrArg (fun r : ℝ => (r:ℂ)) (rowLog_laplacian u hu p hp)
  push_cast at hE hD
  linear_combination
    (deriv (deriv F) (rowHeight u p)*(rowHeight u p:ℂ)^2+
      deriv F (rowHeight u p)*(rowHeight u p:ℂ))*hE+
    (deriv F (rowHeight u p)*(rowHeight u p:ℂ))*hD

open Filter
open scoped BigOperators Classical Topology ContDiff

lemma axisLaplacian_congr_eventuallyEq (f g : SpatialCoordinates → ℂ) (p : SpatialCoordinates)
    (heq : f =ᶠ[𝓝 p] g) : axisLaplacian f p=axisLaplacian g p := by
  have haxis (j : Fin 3) : axisSlice f p j =ᶠ[𝓝 (p j)] axisSlice g p j := by
    have ht : Tendsto (fun x => Function.update p j x) (𝓝 (p j)) (𝓝 p) := by
      have h : Tendsto (fun x => Function.update p j x) (𝓝 (p j)) (𝓝 (Function.update p j (p j))) :=
        (continuous_axis_update p j).continuousAt
      simpa only [Function.update_eq_self] using h
    exact heq.comp_tendsto ht
  unfold axisLaplacian
  congr 1
  · congr 1
    exact Finset.sum_congr rfl (fun j _ => (haxis j).deriv.deriv_eq)
  · rw [(haxis 2).deriv_eq]

lemma axisLaplacian_const_mul (c : ℂ) (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) :
    axisLaplacian (fun q => c*f q) p=c*axisLaplacian f p := by
  unfold axisLaplacian
  simp only [Fin.sum_univ_three]
  unfold axisSlice
  simp only [deriv_const_mul_field',deriv_const_mul_field]
  ring

lemma axisLaplacian_finset_sum {ι : Type*} (S : Finset ι) (f : ι → SpatialCoordinates → ℂ)
    (hreg : ∀i∈S,∀q,0<q 2→∀j : Fin 3,
      DifferentiableAt ℝ (axisSlice (f i) q j) (q j) ∧
      DifferentiableAt ℝ (deriv (axisSlice (f i) q j)) (q j))
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => ∑i∈S,f i q) p=∑i∈S,axisLaplacian (f i) p := by
  have hpair (j : Fin 3) :
      deriv (axisSlice (fun q => ∑i∈S,f i q) p j) (p j)=∑i∈S,deriv (axisSlice (f i) p j) (p j) ∧
      deriv (deriv (axisSlice (fun q => ∑i∈S,f i q) p j)) (p j)=
        ∑i∈S,deriv (deriv (axisSlice (f i) p j)) (p j) := by
    have hfirst (x : ℝ) (hx : 0<(Function.update p j x) 2) :
        HasDerivAt (axisSlice (fun q => ∑i∈S,f i q) p j)
          (∑i∈S,deriv (axisSlice (f i) p j) x) x := by
      have hi (i : ι) (hiS : i∈S) : DifferentiableAt ℝ (axisSlice (f i) p j) x := by
        simpa only [axisSlice_update,Function.update_self] using (hreg i hiS (Function.update p j x) hx j).1
      convert (preTransparency := .instances) HasDerivAt.sum (fun i hiS => (hi i hiS).hasDerivAt) using 1
      ext y
      simp only [axisSlice,Finset.sum_apply]
    have hnear : ∀ᶠx in 𝓝 (p j),0<(Function.update p j x) 2 :=
      ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
        (by simpa only [Function.comp_apply,Function.update_eq_self] using hp)
    have heq : deriv (axisSlice (fun q => ∑i∈S,f i q) p j) =ᶠ[𝓝 (p j)]
        (fun x => ∑i∈S,deriv (axisSlice (f i) p j) x) := by
      filter_upwards [hnear] with x hx
      exact (hfirst x hx).deriv
    have hsecond : HasDerivAt (deriv (axisSlice (fun q => ∑i∈S,f i q) p j))
        (∑i∈S,deriv (deriv (axisSlice (f i) p j)) (p j)) (p j) := by
      apply (HasDerivAt.sum (fun i hiS => (hreg i hiS p hp j).2.hasDerivAt)).congr_of_eventuallyEq
      filter_upwards [heq] with x hx
      simpa only [Finset.sum_apply] using hx
    exact ⟨(hfirst (p j) (by simpa only [Function.comp_apply,Function.update_eq_self] using hp)).deriv,hsecond.deriv⟩
  unfold axisLaplacian
  simp_rw [(hpair _).1,(hpair _).2]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum,Finset.sum_sub_distrib]

end CubicEisenstein

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open Filter
open scoped BigOperators Classical Topology ContDiff

lemma cuspSeed_row_defect (a b : ℝ) (s c : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => c*cuspSeedProfile a b s (rowHeight u q)) p-
      s*(s-2)*(c*cuspSeedProfile a b s (rowHeight u p))=
        c*cuspSeedDefectProfile a b s (rowHeight u p) := by
  rw [axisLaplacian_const_mul,rowProfile_laplacian _ (cuspSeedProfile_contDiffAt a b s) u hu p hp]
  have h := cuspSeedProfile_laplace_defect a b s (rowHeight u p) (rowHeight_pos u hu p hp).ne'
  linear_combination c*h

theorem heightPoincare_cuspSeed_laplace_defect (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (heightPoincareField (cuspSeedProfile a b s)) p-
      s*(s-2)*heightPoincareField (cuspSeedProfile a b s) p=
        heightPoincareField (cuspSeedDefectProfile a b s) p := by
  obtain ⟨U,hU,hpU,S,hrows⟩ := locally_finite_high_rows p hp
  let f : CuspCosets → SpatialCoordinates → ℂ :=
    fun r q => (cosetCharacter r)⁻¹*cuspSeedProfile a b s (rowHeight (embeddedRow r) q)
  have heq : heightPoincareField (cuspSeedProfile a b s) =ᶠ[𝓝 p] (fun q => ∑r∈S,f r q) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    apply tsum_eq_sum
    intro r hr
    rw [cuspSeedProfile_zero a b s _ hab (le_trans ((hrows q hq).2 r hr).le ha.le),mul_zero]
  have hD : heightPoincareField (cuspSeedDefectProfile a b s) p=
      ∑r∈S,(cosetCharacter r)⁻¹*cuspSeedDefectProfile a b s (rowHeight (embeddedRow r) p) := by
    apply tsum_eq_sum
    intro r hr
    rw [cuspSeedDefectProfile_zero a b s _ hab (Or.inl (((hrows p hpU).2 r hr).trans ha)),mul_zero]
  have hreg : ∀r∈S,∀q,0<q 2→∀j : Fin 3,
      DifferentiableAt ℝ (axisSlice (f r) q j) (q j) ∧
      DifferentiableAt ℝ (deriv (axisSlice (f r) q j)) (q j) := by
    intro r hr q hq j
    have hc : ∀v,0<v→ ContDiffAt ℝ ∞ (fun v => (cosetCharacter r)⁻¹*cuspSeedProfile a b s v) v :=
      fun v hv => contDiffAt_const.mul (cuspSeedProfile_contDiffAt a b s v hv)
    have h := rowProfile_axis_derivatives _ hc (embeddedRow r) (embeddedRow_ne_zero r) q hq j
    exact ⟨h.1.differentiableAt,h.2.differentiableAt⟩
  rw [axisLaplacian_congr_eventuallyEq _ _ p heq,axisLaplacian_finset_sum S f hreg p hp,
    heq.eq_of_nhds,hD,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  exact cuspSeed_row_defect a b s (cosetCharacter r)⁻¹ (embeddedRow r) (embeddedRow_ne_zero r) p hp

def smoothCuspSeedField (a b : ℝ) (s : ℂ) (p : SpatialCoordinates) : ℂ :=
  if hp : 0<p 2 then smoothCuspSeed a b s
    (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) else 0

def smoothCuspSeedDefectField (a b : ℝ) (s : ℂ) (p : SpatialCoordinates) : ℂ :=
  if hp : 0<p 2 then smoothCuspSeedDefect a b s
    (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) else 0

lemma smoothCuspSeedField_eq (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeedField a b s p=heightPoincareField (cuspSeedProfile a b s) p := by
  rw [smoothCuspSeedField,dif_pos hp,smoothCuspSeed_coordinate a b s ha hab p hp]
lemma smoothCuspSeedDefectField_eq (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeedDefectField a b s p=heightPoincareField (cuspSeedDefectProfile a b s) p := by
  rw [smoothCuspSeedDefectField,dif_pos hp,smoothCuspSeedDefect_coordinate a b s ha hab p hp]

lemma actual_smoothCuspSeed_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) : ContDiffAt ℝ ∞ (smoothCuspSeedField a b s) p := by
  have heq : smoothCuspSeedField a b s =ᶠ[𝓝 p] heightPoincareField (cuspSeedProfile a b s) := by
    filter_upwards [(continuous_apply 2).continuousAt.eventually_const_lt hp] with q hq
    exact smoothCuspSeedField_eq a b s ha hab q hq
  exact (smoothCuspSeed_contDiffAt a b s ha hab p hp).congr_of_eventuallyEq heq

theorem actual_smoothCuspSeed_laplace_defect (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (smoothCuspSeedField a b s) p-s*(s-2)*smoothCuspSeedField a b s p=
      smoothCuspSeedDefectField a b s p := by
  rw [axisLaplacian_congr_positive _ _ (fun q hq => smoothCuspSeedField_eq a b s ha hab q hq) p hp,
    smoothCuspSeedField_eq a b s ha hab p hp,smoothCuspSeedDefectField_eq a b s ha hab p hp]
  exact heightPoincare_cuspSeed_laplace_defect a b s ha hab p hp

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

def sectorBadIdeal (E : fixedBadPrimes.powerset) : Ideal O := ∏ P ∈ E.val, P

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedPairTerm (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (i : m) (j : n) (k : p) : ℂ :=
  if IsCoprime (left j) (right k) then
    star (a j) * b k * unrestrictedPairCharacter (left j) (right k) (rows i) else 0

def unrestrictedDualTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    (((M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) : ℂ) *
      middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ)))) (Y i) (Z i) lengthScale)

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss

def dualMiddleMajorant {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) : ℝ :=
  ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
    ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
      divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
        (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2)))

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

end CanonicalQuadraticSieve

open scoped BigOperators Classical

open scoped BigOperators Classical

end

end OAI
end

section

namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum

def smallPrincipalMajorant {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ) : ℝ :=
  ((columnDyadicLength N+1:ℕ):ℝ)^2 *
    (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
      (M/F+(2*U)*Real.sqrt (M/F)*B^(α-1/2)))

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedSmallPrincipalSum
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    ∑ d ∈ idealDivisors (left j*right k), if P d i then
      (UniqueFactorizationMonoid.moebius d:ℂ)*
        ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ) else 0

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def maskedPrincipalDivisorCorrection (G : Ideal O)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Z : m → ℝ) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    ∑ d ∈ idealDivisors (G*(left j*right k)), if Z i < (Ideal.absNorm d:ℝ) then
      (UniqueFactorizationMonoid.moebius d:ℂ)*
        ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedLargePrincipalSum
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Z : m → ℝ) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    ∑ d ∈ idealDivisors (left j*right k), if Z i < (Ideal.absNorm d:ℝ) then
      (UniqueFactorizationMonoid.moebius d:ℂ)*
        ((Real.sqrt ((M/F)/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
def unrestrictedDualPrincipalErrorSum (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M F N T : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows cols cols a a i j k *
    (((M / (Real.sqrt ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) * F) : ℝ) : ℂ) *
      truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4))

end CanonicalQuadraticSieve

end

end OAI
end

section

namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

def primePoolDensity (G : Ideal O) : ℂ :=
  ∏ P : primePool {G}, (1-(1:ℂ)/(Ideal.absNorm P.val:ℂ))

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedPrincipalDensity
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (R : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    ((Real.sqrt (R/(Ideal.absNorm (rows i):ℝ)):ℝ):ℂ)*primePoolDensity (left j*right k)

def unrestrictedDualPrincipalTruncation (W : ℝ → ℂ)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Z : m → ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    (((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ) *
      principalTruncation (fun P : primePool {left j*right k} => P.val) Finset.univ W
        (Real.sqrt (F*(Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ)/
          (M*(Ideal.absNorm (rows i):ℝ)))) (Z i))

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

section
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def retainedDualPrincipalSum (W : 𝓢(ℝ,ℂ))
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (M F : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows cols cols a a i j k *
    (((M/(Real.sqrt ((Ideal.absNorm (cols j):ℝ)*(Ideal.absNorm (cols k):ℝ))*F):ℝ):ℂ) *
      dualPrincipalIdeal (cols j) (cols k) W
        (Real.sqrt (F*(Ideal.absNorm (cols j):ℝ)*(Ideal.absNorm (cols k):ℝ)/
          (M*(Ideal.absNorm (rows i):ℝ)))))

end

def retainedDualMajorant {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  ‖paperRadialFourier W 0‖*(4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a a) +
  ‖W 0‖*(4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F T a a) +
  4*dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F T a a W +
  16384*B*N*((2*M/(F*N))*((supportConstant ε hε*(N*N)^ε)*
    (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l))*∑ j, ‖a j‖^2

end

open scoped BigOperators Classical
open ActualEisensteinCubic QuadraticSquarefreeKernel CompletedGauss

def highSquareParts (M K : ℝ) : Finset (Ideal O) := (highKernelRange M K).image squarePart

def highSquarePartFiber (M K : ℝ) (A : Ideal O) : Finset (Ideal O) :=
  (highKernelRange M K).filter (fun I => squarePart I = A)

end CanonicalQuadraticSieve

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
  have hr : 0< r := Real.sqrt_pos.mpr hq
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
    periodLattice.toAddSubgroup.isClosed_of_discrete
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

lemma integral_height_action_matrix (M : SL(2,O)) (g : SL(2,ℂ)) :
    hyperbolicHeight (integralComplexMatrix M • (QuotientGroup.mk g : HyperbolicSpace))=
      (integralRowEnergy g (integralBottomRow M))⁻¹ := by
  change (rowEnergy (complexBottomRow (integralComplexMatrix M*g)))⁻¹=_
  rw [complexBottomRow_mul]
  rfl

lemma integralRowEnergy_bottom_pos (g : SL(2,ℂ)) (M : SL(2,O)) :
    0 < integralRowEnergy g (integralBottomRow M) := by
  have h := hyperbolicHeight_pos (integralComplexMatrix M • (QuotientGroup.mk g : HyperbolicSpace))
  rw [integral_height_action_matrix,inv_pos] at h
  exact h

theorem exists_maximal_integral_height (w : HyperbolicSpace) :
    ∃N : SL(2,O), ∀M : SL(2,O),
      hyperbolicHeight (integralComplexMatrix M • w)≤hyperbolicHeight (integralComplexMatrix N • w) := by
  induction w using Quotient.inductionOn with
  | _ g =>
    let P : Set (Fin 2 → O) := Set.range integralBottomRow
    let C := integralRowEnergy g (integralBottomRow 1)
    let S : Set (Fin 2 → O) := {v | integralRowEnergy g v≤C} ∩ P
    have hS : Set.Finite S := (integralRowEnergy_sublevel_finite g C).inter_of_left P
    have hSne : S.Nonempty := by
      refine ⟨integralBottomRow 1,?_⟩
      change C≤C ∧ integralBottomRow 1∈Set.range integralBottomRow
      exact ⟨le_rfl,1,rfl⟩
    obtain ⟨v,hv,hmin⟩ := Set.exists_min_image S (integralRowEnergy g) hS hSne
    obtain ⟨N,hN⟩ := hv.2
    refine ⟨N,fun M => ?_⟩
    have hNM : integralRowEnergy g (integralBottomRow N)≤ integralRowEnergy g (integralBottomRow M) := by
      rw [hN]
      by_cases hM : integralRowEnergy g (integralBottomRow M)≤C
      · exact hmin _ ⟨hM,⟨M,rfl⟩⟩
      · exact hv.1.trans (le_of_not_ge hM)
    rw [integral_height_action_matrix,integral_height_action_matrix]
    exact inv_anti₀ (integralRowEnergy_bottom_pos g N) hNM

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def integralTranslation (n : O) : SL(2,O) :=
  ⟨!![1,n;0,1],by simp [Matrix.det_fin_two]⟩
def integralInversion : SL(2,O) :=
  ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩

lemma integralTranslation_action (n : O) (z : ℂ) (v : ℝ) (hv : 0<v) :
    integralComplexMatrix (integralTranslation n) • upperPoint z v hv=
      upperPoint (z+eisEmbedding n) v hv := by
  change (QuotientGroup.mk (integralComplexMatrix (integralTranslation n)*upperSection z v hv) : HyperbolicSpace)=
    QuotientGroup.mk (upperSection (z+eisEmbedding n) v hv)
  apply congrArg (fun g : SL(2,ℂ) => (QuotientGroup.mk g : HyperbolicSpace))
  apply Subtype.ext
  change (integralComplexMatrix (integralTranslation n) : Matrix (Fin 2) (Fin 2) ℂ) *
    (upperSection z v hv : Matrix (Fin 2) (Fin 2) ℂ) =
    (upperSection (z + eisEmbedding n) v hv : Matrix (Fin 2) (Fin 2) ℂ)
  simp only [integralComplexMatrix, Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [integralTranslation,RingHom.mapMatrix_apply,Matrix.map_apply,upperSection,Matrix.mul_apply,
      Fin.sum_univ_two,div_eq_mul_inv] ; ring

lemma integralInversion_height (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHeight (integralComplexMatrix integralInversion • upperPoint z v hv)=
      v/(‖z‖^2+v^2) := by
  have h10 : integralComplexMatrix integralInversion 1 0 = 1 := by
    change eisEmbedding 1 = 1
    exact map_one eisEmbedding
  have h11 : integralComplexMatrix integralInversion 1 1 = 0 := by
    change eisEmbedding 0 = 0
    exact map_zero eisEmbedding
  rw [hyperbolicHeight_action_upperPoint, h10, h11]
  simp

theorem bianchi_ford_cover (w : HyperbolicSpace) :
    ∃M : SL(2,O), ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
      integralComplexMatrix M • w=upperPoint z v hv ∧
      Complex.normSq z≤1/3 ∧ 1≤Complex.normSq z+v^2 ∧
      ∀R : SL(2,O),hyperbolicHeight (integralComplexMatrix R • upperPoint z v hv)≤v := by
  obtain ⟨N,hN⟩ := exists_maximal_integral_height w
  obtain ⟨z,v,hv,hpoint⟩ := upperPoint_surjective (integralComplexMatrix N • w)
  obtain ⟨n,hn⟩ := exists_eisenstein_distance_sq_le_third z
  let M : SL(2,O) := integralTranslation (-n)*N
  let z' := z-eisEmbedding n
  have hMw : integralComplexMatrix M • w=upperPoint z' v hv := by
    dsimp [M]
    rw [map_mul,mul_smul,← hpoint,integralTranslation_action,map_neg]
    rfl
  have hNv : hyperbolicHeight (integralComplexMatrix N • w)=v := by
    rw [← hpoint,hyperbolicHeight_upperPoint]
  have hmax (R : SL(2,O)) :
      hyperbolicHeight (integralComplexMatrix R • upperPoint z' v hv)≤v := by
    have h := hN (R*M)
    rwa [map_mul,mul_smul,hMw,hNv] at h
  have hinv := hmax integralInversion
  rw [integralInversion_height] at hinv
  have hden : 0<‖z'‖^2+v^2 := by positivity
  have hunit : 1≤‖z'‖^2+v^2 := by
    have hm := (div_le_iff₀ hden).mp hinv
    by_contra hh
    have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge hh) hv
    linarith
  refine ⟨M,z',v,hv,hMw,hn,?_,hmax⟩
  simpa only [Complex.normSq_eq_norm_sq] using hunit

theorem bianchi_reduction_height_floor (w : HyperbolicSpace) :
    ∃M : SL(2,O), ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
      integralComplexMatrix M • w=upperPoint z v hv ∧
      Complex.normSq z≤1/3 ∧ Real.sqrt (2/3)≤v := by
  obtain ⟨M,z,v,hv,hMw,hz,hunit,hmax⟩ := bianchi_ford_cover w
  refine ⟨M,z,v,hv,hMw,hz,?_⟩
  apply (Real.sqrt_le_iff).mpr
  exact ⟨hv.le,by linarith⟩

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

theorem finiteIndex_ford_cover (H : Subgroup (SL(2,O))) [H.FiniteIndex] :
    ∃S : Finset (SL(2,O)), ∀w : HyperbolicSpace,
      ∃h : H, ∃r∈S, ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
        integralComplexMatrix (h:SL(2,O)) • w=
          integralComplexMatrix r⁻¹ • upperPoint z v hv ∧
        Complex.normSq z≤1/3 ∧ Real.sqrt (2/3)≤v := by
  obtain ⟨S,hS⟩ := finite_right_representatives H
  refine ⟨S,fun w => ?_⟩
  obtain ⟨M,z,v,hv,hMw,hz,hfloor⟩ := bianchi_reduction_height_floor w
  obtain ⟨r,hr,hh⟩ := hS M
  refine ⟨⟨r⁻¹*M,hh⟩,r,hr,z,v,hv,?_,hz,hfloor⟩
  change integralComplexMatrix (r⁻¹*M) • w=_
  rw [map_mul,mul_smul,hMw]

end CubicEisenstein

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

theorem globalKubotaKernel_compact_core_cusp_cover :
    ∃S : Finset (SL(2,O)), ∀T : ℝ,
      IsCompact (compactFordCore globalKubotaKernel S T) ∧
      Set.univ=compactFordCore globalKubotaKernel S T ∪ ⋃r∈S, fordCuspTail globalKubotaKernel r T := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact finiteIndex_compact_core_cusp_cover globalKubotaKernel

end CubicEisenstein

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

def sourcePrincipalScale (M : ℝ) (I : Ideal O) : ℝ := Real.sqrt (M/(Ideal.absNorm I:ℝ))

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def maskedSourceDensity (G : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (M : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    ((sourcePrincipalScale M (rows i):ℝ):ℂ)*primePoolDensity (G*(cols j*cols k))

def maskedPrincipalSourceSum (G : Ideal O) (W : 𝓢(ℝ,ℂ))
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (M : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    ∑' z : O, rowCoprimeMask (fun P : primePool {G*(cols j*cols k)} => P.val) Finset.univ z *
      (if z=0 then 0 else W (‖eisEmbedding z‖^2/sourcePrincipalScale M (rows i)))

def maskedSourcePrincipalTruncation (G : Ideal O) (W : 𝓢(ℝ,ℂ))
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (M : ℝ) (Z : m → ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    principalTruncation (fun P : primePool {G*(cols j*cols k)} => P.val) Finset.univ W
      (sourcePrincipalScale M (rows i)) (Z i)

def maskedSourceErrorSum (G : Ideal O) (W : 𝓢(ℝ,ℂ))
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (M T : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    truncationError (fun P : primePool {G*(cols j*cols k)} => P.val) Finset.univ W
      (sourcePrincipalScale M (rows i))
      (sourcePrincipalScale M (rows i)/T)
      (T*sourcePrincipalScale M (rows i)) (T^4)

end
section

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator IdealMobiusDivisorSum

def sourcePrincipalMajorant {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (G : Ideal O) (B N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  ‖paperRadialFourier W 0‖*((idealDivisors G).card *
    (((columnDyadicLength N+1:ℕ):ℝ)^2 *
      (2*divisorEnergyFactor ε hε N a a*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (4*N/T+Real.sqrt M*B^(α-1/2))))) +
  (idealDivisors G).card * (((columnDyadicLength N+1:ℕ):ℝ)^2 *
    ((2*nonzeroLatticeEnvelopeConstant*originalMiddleDecayConstant W)*
      divisorEnergyFactor ε hε N a a*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (N+(2*T)*Real.sqrt M*B^(α-1/2)))) +
  16384*B*N*((supportConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε)*
    (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l)*∑ j, ‖a j‖^2

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

end

open ActualEisensteinCubic

def densityColumn {n : Type*} (cols : n → Ideal O) (a : n → ℂ) : n → ℂ :=
  fun j => primePoolDensity (cols j) * a j

open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss IdealMobiusDivisorSum

def densityPairSum {n : Type} [Fintype n] (cols : n → Ideal O) (a : n → ℂ)
    (P : Ideal O → Ideal O → ℂ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j)*a k*primePoolDensity (cols j*cols k)*P (cols j) (cols k) else 0

end CanonicalQuadraticSieve

end

end OAI
end

section

namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex IdealMobiusDivisorSum

def maskedPairDualTail (G I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) : ℂ :=
  ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
    ∑ q ∈ idealDivisors G,
      ((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
        dualSquarefreeTail I J W
          (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K

def retainedDualPair (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M F K : ℝ) : ℂ :=
  ∑ B : squarefreeIdealRange K, unrestrictedPairCharacter I J B.val*
    (((M/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))*F):ℝ):ℂ)*
      dualPrincipalIdeal I J W
        (Real.sqrt (F*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)/(M*(Ideal.absNorm B.val:ℝ)))))

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

def maskedDualFamily {n : Type} [Fintype n]
    (G : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j)*a k*maskedPairIdealDualKernel G (cols j) (cols k) W M else 0

def maskedDualTailFamily {n : Type} [Fintype n]
    (G : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j)*a k*maskedPairDualTail G (cols j) (cols k) W M K else 0

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum

def pairMaskedSquareSource (G I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M : ℝ) (B : Ideal O) : ℂ :=
  (quadraticRow I (primaryGenerator B)*quadraticRow J (primaryGenerator B))*
    ∑' z : O, rowCoprimeMask (fun P : primePool {G*(I*J)} => P.val) Finset.univ z *
      (if z=0 then 0 else quadraticSquareProfile W (‖eisEmbedding z‖^2/sourcePrincipalScale M B))

end

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

def gcdRaySupport {n : Type} [Fintype n] (cols : n → Ideal O) (a : n → ℂ)
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) : Finset n :=
  Finset.univ.filter (fun j => D ∣ cols j ∧ columnRay (cols j)=c ∧ a j≠0)

end CanonicalQuadraticSieve

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace CanonicalQuadraticSieve

section

def bootstrapExponent (n : ℕ) : ℝ := 1+1/((n:ℝ)+1)

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

def divisorTwist {n : Type} (cols : n → Ideal O) (a : n → ℂ) (q : Ideal O) : n → ℂ :=
  fun j => a j*quadraticRow (cols j) (idealGenerator q)

def centeredRetainedDual {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) (q : Ideal O) : ℂ :=
  (6:ℂ)*retainedDualPrincipalSum (quadraticTransformedSquareProfile W)
    (fun I : squarefreeIdealRange K => I.val) cols (divisorTwist cols a q) M (Ideal.absNorm q:ℝ) -
  paperRadialFourier (quadraticTransformedSquareProfile W) 0 *
    unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
      (divisorTwist cols a q) (divisorTwist cols a q) (M/(Ideal.absNorm q:ℝ))

def centeredMaskedSource {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) : ℂ :=
  maskedPrincipalSourceSum G (quadraticSquareProfile W)
    (fun I : coprimeSquarefreeRange G K => I.val) cols a M -
  paperRadialFourier (quadraticSquareProfile W) 0 *
    maskedSourceDensity G (fun I : coprimeSquarefreeRange G K => I.val) cols a M

def maskedPoissonDifference {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) : ℂ :=
  maskedDualFamily G cols a W M - (6:ℂ)⁻¹ *
    maskedPrincipalSourceSum G (quadraticSquareProfile W)
      (fun I : coprimeSquarefreeRange G K => I.val) cols a M

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator

end

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator

def poissonComparisonMajorant {n : Type} [Fintype n]
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  (idealDivisors G).card*(columnDyadicLength K+1:ℕ)*
    retainedDualMajorant sD CD l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) +
  6*(256*M*(idealDivisors G).card*
    ((CT*sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
      ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
        (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A))*∑j, ‖a j‖^2) +
  (columnDyadicLength K+1:ℕ)*
    sourcePrincipalMajorant sS CS l hexp deltaLoss hδ ε hε G (2*K) N M T a (quadraticSquareProfile W) +
  ‖paperRadialFourier (quadraticSquareProfile W) 0‖ *
    (((idealDivisors G).card:ℝ)^2*(supportConstant ε hε*N^ε)*CP*(K*N)^deltaLoss*
      (Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2))*∑j, ‖a j‖^2)

end

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy

end CanonicalQuadraticSieve

open scoped BigOperators Classical

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

def activeGcdColumns (N : ℝ) (a : idealRange N → ℂ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    gcdRaySupport (fun I : idealRange N => I.val) a D c → Ideal O :=
  fun j => idealQuotient D j.val.val

def activeGcdCoefficient (N : ℝ) (a : idealRange N → ℂ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    gcdRaySupport (fun I : idealRange N => I.val) a D c → ℂ := fun j => a j.val

end

def selectedPoissonT (C M X η : ℝ) : ℝ := C*(M*X)^η
def selectedPoissonK (C M X η : ℝ) : ℝ := selectedPoissonT C M X η*X^2/M

end CanonicalQuadraticSieve

open Filter MeasureTheory EuclideanGeometry
open scoped BigOperators Classical Topology InnerProductSpace ENNReal

namespace CubicEisenstein

abbrev EuclideanSpatial := EuclideanSpace ℝ (Fin 3)

def euclideanUpperHalf : Set EuclideanSpatial := {p | 0<p 2}
def hyperbolicDensity (p : EuclideanSpatial) : ℝ≥0∞ := ENNReal.ofReal ((p 2)^3)⁻¹

def hyperbolicEuclideanVolume : Measure EuclideanSpatial :=
  (volume.restrict euclideanUpperHalf).withDensity hyperbolicDensity

lemma euclideanUpperHalf_measurable : MeasurableSet euclideanUpperHalf := by
  exact measurableSet_lt measurable_const (by fun_prop)

lemma hyperbolicDensity_measurable : Measurable hyperbolicDensity := by
  unfold hyperbolicDensity
  fun_prop

lemma hyperbolic_volume_map_of_jacobian
    (f : EuclideanSpatial → EuclideanSpatial)
    (df : EuclideanSpatial → EuclideanSpatial →L[ℝ] EuclideanSpatial)
    (hf : Measurable f) (hderiv : ∀p∈euclideanUpperHalf,HasFDerivAt f (df p) p)
    (hinj : Set.InjOn f euclideanUpperHalf) (himage : f '' euclideanUpperHalf=euclideanUpperHalf)
    (hjac : ∀p∈euclideanUpperHalf,
      ENNReal.ofReal |(df p).det| *hyperbolicDensity (f p)=hyperbolicDensity p) :
    Measure.map f hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf hs]
  unfold hyperbolicEuclideanVolume
  rw [withDensity_apply _ (hs.preimage hf),withDensity_apply _ hs]
  rw [←lintegral_indicator (hs.preimage hf),←lintegral_indicator hs]
  have hc := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    euclideanUpperHalf_measurable (fun p hp => (hderiv p hp).hasFDerivWithinAt) hinj
    (s.indicator hyperbolicDensity)
  rw [himage] at hc
  rw [hc]
  apply setLIntegral_congr_fun euclideanUpperHalf_measurable
  intro p hp
  by_cases hsfp : f p∈s
  · simp only [Set.indicator_of_mem hsfp,Set.mem_preimage,hsfp,Set.indicator_of_mem]
    exact (hjac p hp).symm
  · simp only [Set.indicator_of_notMem hsfp,mul_zero]
    have hpnot : p∉f ⁻¹' s := hsfp
    exact Set.indicator_of_notMem hpnot hyperbolicDensity

def euclideanInversion : EuclideanSpatial → EuclideanSpatial := inversion 0 1

def euclideanInversionDeriv (p : EuclideanSpatial) : EuclideanSpatial →L[ℝ] EuclideanSpatial :=
  (1/‖p‖)^2 • (((ℝ ∙ p)ᗮ).reflection : EuclideanSpatial →L[ℝ] EuclideanSpatial)

lemma euclideanInversion_apply (p : EuclideanSpatial) (j : Fin 3) :
    euclideanInversion p j=(1/‖p‖)^2*p j := by
  simp [euclideanInversion,inversion,dist_zero_right]

lemma euclideanInversion_measurable : Measurable euclideanInversion := by
  simp +unfoldPartialApp only [euclideanInversion,inversion,dist_zero_right,vsub_eq_sub,sub_zero,vadd_eq_add,add_zero]
  fun_prop

lemma euclideanUpperHalf_ne_zero (p : EuclideanSpatial) (hp : p∈euclideanUpperHalf) : p≠0 := by
  intro he
  simp [euclideanUpperHalf,he] at hp

lemma euclideanInversion_mem (p : EuclideanSpatial) (hp : p∈euclideanUpperHalf) :
    euclideanInversion p∈euclideanUpperHalf := by
  change 0<euclideanInversion p 2
  rw [euclideanInversion_apply]
  exact mul_pos (sq_pos_of_pos (one_div_pos.mpr (norm_pos_iff.mpr (euclideanUpperHalf_ne_zero p hp)))) hp

lemma euclideanInversion_image : euclideanInversion '' euclideanUpperHalf=euclideanUpperHalf := by
  apply Set.Subset.antisymm
  · rintro p ⟨q,hq,rfl⟩
    exact euclideanInversion_mem q hq
  · intro p hp
    exact ⟨euclideanInversion p,euclideanInversion_mem p hp,
      inversion_inversion 0 (by norm_num) p⟩

lemma euclideanInversion_hasFDerivAt (p : EuclideanSpatial) (hp : p≠0) :
    HasFDerivAt euclideanInversion (euclideanInversionDeriv p) p := by
  simpa [euclideanInversion,euclideanInversionDeriv,dist_zero_right] using
    (hasFDerivAt_inversion (R := (1:ℝ)) hp)

lemma euclideanInversion_abs_det (p : EuclideanSpatial) :
    |(euclideanInversionDeriv p).det|=((1/‖p‖)^2)^3 := by
  unfold euclideanInversionDeriv
  change |LinearMap.det ((1/‖p‖)^2 • ((ℝ ∙ p)ᗮ).reflection.toLinearMap)|=_
  rw [LinearMap.det_smul]
  rw [Submodule.det_reflection]
  simp only [finrank_euclideanSpace,Fintype.card_fin,abs_mul,abs_pow,abs_neg,abs_one,
    one_pow,mul_one]
  rw [abs_of_nonneg (one_div_nonneg.mpr (norm_nonneg p))]

lemma euclideanInversion_jacobian_density (p : EuclideanSpatial) (hp : p∈euclideanUpperHalf) :
    ENNReal.ofReal |(euclideanInversionDeriv p).det| *
      hyperbolicDensity (euclideanInversion p)=hyperbolicDensity p := by
  rw [euclideanInversion_abs_det,hyperbolicDensity,hyperbolicDensity,euclideanInversion_apply]
  rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hn : ‖p‖≠0 := norm_ne_zero_iff.mpr (euclideanUpperHalf_ne_zero p hp)
  field_simp

theorem euclideanInversion_preserves_hyperbolicVolume :
    Measure.map euclideanInversion hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply hyperbolic_volume_map_of_jacobian euclideanInversion euclideanInversionDeriv
    euclideanInversion_measurable
  · exact fun p hp => euclideanInversion_hasFDerivAt p (euclideanUpperHalf_ne_zero p hp)
  · exact (inversion_injective 0 (by norm_num : (1:ℝ)≠0)).injOn
  · exact euclideanInversion_image
  · exact euclideanInversion_jacobian_density

end CubicEisenstein

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open Filter MeasureTheory EuclideanGeometry
open scoped BigOperators Classical Topology InnerProductSpace ENNReal Matrix

lemma linear_preserves_hyperbolicVolume (A : EuclideanSpatial →L[ℝ] EuclideanSpatial)
    (k : ℝ) (hk : 0<k) (hh : ∀p,(A p) 2=k*p 2) (hd : |A.det|=k^3) :
    Measure.map A hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  have hdet : A.det≠0 := by intro he; rw [he,abs_zero] at hd; exact (pow_ne_zero 3 hk.ne') hd.symm
  have hker : LinearMap.ker A.toLinearMap=⊥ := by
    by_contra hn
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hn)
  have hinj : Function.Injective A := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective A := (LinearMap.injective_iff_surjective).mp hinj
  apply hyperbolic_volume_map_of_jacobian A (fun _ => A) A.continuous.measurable
    (fun p hp => A.hasFDerivAt) hinj.injOn
  · apply Set.Subset.antisymm
    · rintro q ⟨p,hp,rfl⟩
      exact show 0<(A p) 2 by rw [hh]; exact mul_pos hk hp
    · intro q hq
      obtain ⟨p,hp⟩ := hsurj q
      refine ⟨p,?_,hp⟩
      change 0<p 2
      have h := hh p
      rw [hp] at h
      exact (mul_pos_iff_of_pos_left hk).mp (h.symm ▸ hq)
  · intro p hp
    rw [hd,hyperbolicDensity,hyperbolicDensity,hh]
    rw [←ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp

lemma translation_preserves_hyperbolicVolume (u : EuclideanSpatial) (hu : u 2=0) :
    Measure.map (fun p => p+u) hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply hyperbolic_volume_map_of_jacobian (fun p => p+u) (fun _ => ContinuousLinearMap.id ℝ _)
    (continuous_id.add continuous_const).measurable
    (fun p hp => (hasFDerivAt_id p).add_const u) (add_left_injective u).injOn
  · apply Set.Subset.antisymm
    · rintro q ⟨p,hp,rfl⟩
      simpa [euclideanUpperHalf,hu] using hp
    · intro p hp
      refine ⟨p-u,?_,sub_add_cancel p u⟩
      simpa [euclideanUpperHalf,hu] using hp
  · intro p hp
    have hid : (ContinuousLinearMap.id ℝ EuclideanSpatial).det=1 := by
      change LinearMap.det (LinearMap.id : EuclideanSpatial →ₗ[ℝ] EuclideanSpatial)=1
      simp
    simp [hyperbolicDensity,hu,hid]

def euclideanMatrixOperator (M : Matrix (Fin 3) (Fin 3) ℝ) :
    EuclideanSpatial →L[ℝ] EuclideanSpatial := M.toEuclideanLin.toContinuousLinearMap

lemma euclideanMatrixOperator_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (p : EuclideanSpatial)
    (j : Fin 3) : euclideanMatrixOperator M p j=∑i,M j i*p i := rfl

lemma euclideanMatrixOperator_det (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (euclideanMatrixOperator M).det=M.det := by
  change LinearMap.det (Matrix.toEuclideanLin M)=M.det
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin]

def euclideanWeylReflection : EuclideanSpatial →L[ℝ] EuclideanSpatial :=
  euclideanMatrixOperator !![-1,0,0;0,1,0;0,0,1]

lemma euclideanWeylReflection_apply (p : EuclideanSpatial) :
    euclideanWeylReflection p 0= -p 0 ∧ euclideanWeylReflection p 1=p 1 ∧
      euclideanWeylReflection p 2=p 2 := by
  simp [euclideanWeylReflection,euclideanMatrixOperator_apply,Fin.sum_univ_three]

lemma euclideanWeylReflection_preserves_hyperbolicVolume :
    Measure.map euclideanWeylReflection hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply linear_preserves_hyperbolicVolume euclideanWeylReflection 1 (by norm_num)
  · intro p
    simpa using (euclideanWeylReflection_apply p).2.2
  · ((try simp [euclideanWeylReflection,euclideanMatrixOperator_det,Matrix.det_fin_three]) <;> norm_num [euclideanWeylReflection,euclideanMatrixOperator_det,Matrix.det_fin_three])

def euclideanComplexDilation (β : ℂ) : EuclideanSpatial →L[ℝ] EuclideanSpatial :=
  euclideanMatrixOperator !![(β^2).re,-(β^2).im,0;(β^2).im,(β^2).re,0;0,0,Complex.normSq β]

lemma euclideanComplexDilation_apply (β : ℂ) (p : EuclideanSpatial) :
    euclideanComplexDilation β p 0=(β^2).re*p 0-(β^2).im*p 1 ∧
      euclideanComplexDilation β p 1=(β^2).im*p 0+(β^2).re*p 1 ∧
      euclideanComplexDilation β p 2=Complex.normSq β*p 2 := by
  simp [euclideanComplexDilation,euclideanMatrixOperator_apply,Fin.sum_univ_three,sub_eq_add_neg]

lemma euclideanComplexDilation_det (β : ℂ) :
    (euclideanComplexDilation β).det=Complex.normSq β^3 := by
  rw [euclideanComplexDilation,euclideanMatrixOperator_det,Matrix.det_fin_three]
  have h : (β^2).re^2+(β^2).im^2=(Complex.normSq β)^2 := by
    simpa [Complex.normSq_apply,sq] using map_pow Complex.normSq β 2
  change (β^2).re*(β^2).re*Complex.normSq β-(β^2).re*0*0-
    (-(β^2).im)*(β^2).im*Complex.normSq β+(-(β^2).im)*0*0+
    0*(β^2).im*0-0*(β^2).re*0=Complex.normSq β^3
  calc
    _ = ((β^2).re^2+(β^2).im^2)*Complex.normSq β := by ring
    _ = _ := by rw [h]; ring

lemma euclideanComplexDilation_preserves_hyperbolicVolume (β : ℂ) (hβ : β≠0) :
    Measure.map (euclideanComplexDilation β) hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply linear_preserves_hyperbolicVolume (euclideanComplexDilation β) (Complex.normSq β)
    (Complex.normSq_pos.mpr hβ) (fun p => (euclideanComplexDilation_apply β p).2.2)
  rw [euclideanComplexDilation_det,abs_of_nonneg (pow_nonneg (Complex.normSq_nonneg β) 3)]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein

instance hyperbolicMeasurableSpace : MeasurableSpace HyperbolicSpace := borel HyperbolicSpace
instance hyperbolicBorelSpace : BorelSpace HyperbolicSpace := ⟨rfl⟩

lemma continuous_hyperbolic_action (g : SL(2,ℂ)) :
    Continuous (fun w : HyperbolicSpace => g • w) := by
  apply (QuotientGroup.isQuotientMap_mk compactSubgroup).continuous_iff.mpr
  exact continuous_hyperbolicProjection.comp (continuous_complexSL_mul g)

def positiveCoordinateHeight (p : EuclideanSpatial) : ℝ := if 0<p 2 then p 2 else 1
lemma positiveCoordinateHeight_pos (p : EuclideanSpatial) : 0<positiveCoordinateHeight p := by
  unfold positiveCoordinateHeight
  split_ifs with hp
  · exact hp
  · norm_num

def euclideanToUpperCoordinates (p : EuclideanSpatial) : UpperCoordinates :=
  ⟨((p 0:ℂ)+Complex.I*(p 1:ℂ),positiveCoordinateHeight p),positiveCoordinateHeight_pos p⟩

def euclideanToHyperbolic (p : EuclideanSpatial) : HyperbolicSpace :=
  upperPoint (euclideanToUpperCoordinates p).1.1 (euclideanToUpperCoordinates p).1.2
    (euclideanToUpperCoordinates p).2

lemma euclideanToUpperCoordinates_measurable : Measurable euclideanToUpperCoordinates := by
  apply Measurable.subtype_mk
  apply Measurable.prodMk
  · change Measurable (fun p : EuclideanSpatial => (p 0:ℂ)+Complex.I*(p 1:ℂ))
    fun_prop
  · exact Measurable.ite euclideanUpperHalf_measurable (by fun_prop) measurable_const

lemma euclideanToHyperbolic_measurable : Measurable euclideanToHyperbolic :=
  continuous_upperCoordinates.measurable.comp euclideanToUpperCoordinates_measurable

lemma euclideanToHyperbolic_positive (p : EuclideanSpatial) (hp : 0<p 2) :
    euclideanToHyperbolic p=upperPoint ((p 0:ℂ)+Complex.I*(p 1:ℂ)) (p 2) hp := by
  unfold euclideanToHyperbolic euclideanToUpperCoordinates positiveCoordinateHeight
  simp only [if_pos hp]

def hyperbolicVolume : Measure HyperbolicSpace :=
  Measure.map euclideanToHyperbolic hyperbolicEuclideanVolume

lemma hyperbolicEuclideanVolume_ae_positive :
    ∀ᵐp∂hyperbolicEuclideanVolume,0<p 2 := by
  exact (ae_restrict_mem euclideanUpperHalf_measurable).filter_mono
    ((withDensity_absolutelyContinuous (volume.restrict euclideanUpperHalf) hyperbolicDensity).ae_le)

lemma hyperbolicVolume_map_of_coordinate_action (g : SL(2,ℂ))
    (f : EuclideanSpatial → EuclideanSpatial) (hf : Measurable f)
    (hvol : Measure.map f hyperbolicEuclideanVolume=hyperbolicEuclideanVolume)
    (hcompat : ∀p,0<p 2 → euclideanToHyperbolic (f p)=g • euclideanToHyperbolic p) :
    Measure.map (fun w => g • w) hyperbolicVolume=hyperbolicVolume := by
  unfold hyperbolicVolume
  rw [Measure.map_map (continuous_hyperbolic_action g).measurable euclideanToHyperbolic_measurable]
  calc
    _ = Measure.map (euclideanToHyperbolic ∘ f) hyperbolicEuclideanVolume := by
      apply Measure.map_congr
      filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
      exact (hcompat p hp).symm
    _ = _ := by rw [←Measure.map_map euclideanToHyperbolic_measurable hf,hvol]

lemma matrix_point_coordinates (g : SL(2,ℂ)) :
    (g : HyperbolicSpace)=upperPoint (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g) := by
  obtain ⟨k,hk,hg⟩ := matrix_iwasawa_factor g
  apply Eq.symm
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  change (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*g∈compactSubgroup
  have hcancel : (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*g=k := by
    calc
      _ = (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*
          (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g)*k) :=
        congrArg (fun M => (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*M) hg
      _ = k := inv_mul_cancel_left _ _
  rwa [hcancel]

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

def matrixCross (g : SL(2,ℂ)) : ℂ := g 0 0*star (g 1 0)+g 0 1*star (g 1 1)

lemma matrixHorizontal_eq_cross_height (g : SL(2,ℂ)) :
    matrixHorizontal g=matrixCross g*(liftedHeight g:ℂ) := by
  unfold matrixHorizontal matrixCross liftedHeight
  rw [Complex.ofReal_inv]
  rfl

lemma matrixCross_upperSection (g : SL(2,ℂ)) (z : ℂ) (v : ℝ) (hv : 0<v) :
    matrixCross (g*upperSection z v hv)=
      ((g 0 0*z+g 0 1)*star (g 1 0*z+g 1 1)+
        g 0 0*star (g 1 0)*(v:ℂ)^2)/(v:ℂ) := by
  have hr : (Real.sqrt v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hv).ne'
  have hrs : (Real.sqrt v:ℂ)^2=(v:ℂ) := by exact_mod_cast Real.sq_sqrt hv.le
  simp only [matrixCross,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  change (g 0 0*(Real.sqrt v:ℂ)+g 0 1*0)*star (g 1 0*(Real.sqrt v:ℂ)+g 1 1*0)+
    (g 0 0*(z/(Real.sqrt v:ℂ))+g 0 1*(Real.sqrt v:ℂ)⁻¹)*
      star (g 1 0*(z/(Real.sqrt v:ℂ))+g 1 1*(Real.sqrt v:ℂ)⁻¹)=_
  simp only [mul_zero,add_zero,star_add,star_mul,Complex.star_def,
    map_inv₀,map_div₀,Complex.conj_ofReal]
  rw [←hrs]
  field_simp
  ; ring

lemma mobius_denominator_pos (g : SL(2,ℂ)) (z : ℂ) (v : ℝ) (hv : 0<v) :
    0<‖g 1 0*z+g 1 1‖^2+‖g 1 0‖^2*v^2 := by
  exact heightDenominator_pos z v hv (complexBottomRow g) (complexBottomRow_ne_zero g)

lemma upperPoint_congr {z z' : ℂ} {v v' : ℝ} (hv : 0<v) (hv' : 0<v')
    (hz : z=z') (hvv : v=v') : upperPoint z v hv=upperPoint z' v' hv' := by
  subst z'
  subst v'
  rfl

theorem mobius_upperPoint (g : SL(2,ℂ)) (z : ℂ) (v : ℝ) (hv : 0<v) :
    g • upperPoint z v hv=
      upperPoint
        (((g 0 0*z+g 0 1)*star (g 1 0*z+g 1 1)+g 0 0*star (g 1 0)*(v:ℂ)^2)/
          ((‖g 1 0*z+g 1 1‖^2+‖g 1 0‖^2*v^2:ℝ):ℂ))
        (v/(‖g 1 0*z+g 1 1‖^2+‖g 1 0‖^2*v^2))
        (div_pos hv (mobius_denominator_pos g z v hv)) := by
  have hh : liftedHeight (g*upperSection z v hv)=
      v/(‖g 1 0*z+g 1 1‖^2+‖g 1 0‖^2*v^2) :=
    hyperbolicHeight_action_upperPoint g z v hv
  change (QuotientGroup.mk (g*upperSection z v hv) : HyperbolicSpace)=_
  rw [matrix_point_coordinates]
  apply upperPoint_congr _ _ _ hh
  rw [matrixHorizontal_eq_cross_height,matrixCross_upperSection,hh,Complex.ofReal_div]
  have hvc : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp

def complexTranslation (b : ℂ) : SL(2,ℂ) := ⟨!![1,b;0,1],by simp [Matrix.det_fin_two]⟩
def complexDiagonal (b : ℂ) (hb : b≠0) : SL(2,ℂ) :=
  ⟨!![b,0;0,b⁻¹],by simp [Matrix.det_fin_two,hb]⟩
def complexWeyl : SL(2,ℂ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩

lemma complexTranslation_action (b z : ℂ) (v : ℝ) (hv : 0<v) :
    complexTranslation b • upperPoint z v hv=upperPoint (z+b) v hv := by
  change (QuotientGroup.mk (complexTranslation b*upperSection z v hv) : HyperbolicSpace)=
    QuotientGroup.mk (upperSection (z+b) v hv)
  apply congrArg (fun g : SL(2,ℂ) => (QuotientGroup.mk g : HyperbolicSpace))
  apply Subtype.ext
  change (complexTranslation b : Matrix (Fin 2) (Fin 2) ℂ) *
    (upperSection z v hv : Matrix (Fin 2) (Fin 2) ℂ) =
    (upperSection (z + b) v hv : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation,upperSection,Matrix.mul_apply,
      Fin.sum_univ_two,div_eq_mul_inv] ; ring

lemma complexWeyl_action (z : ℂ) (v : ℝ) (hv : 0<v) :
    complexWeyl • upperPoint z v hv=
      upperPoint (-star z/((‖z‖^2+v^2:ℝ):ℂ)) (v/(‖z‖^2+v^2))
        (div_pos hv (by nlinarith [sq_nonneg ‖z‖])) := by
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · simp [complexWeyl]
  · simp [complexWeyl]

lemma complexDiagonal_action (b : ℂ) (hb : b≠0) (z : ℂ) (v : ℝ) (hv : 0<v) :
    complexDiagonal b hb • upperPoint z v hv=
      upperPoint (b^2*z) (Complex.normSq b*v) (mul_pos (Complex.normSq_pos.mpr hb) hv) := by
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · change ((b*z+0)*star (0*z+b⁻¹)+b*star 0*(v:ℂ)^2)/
        ((‖0*z+b⁻¹‖^2+‖(0:ℂ)‖^2*v^2:ℝ):ℂ)=b^2*z
    simp only [zero_mul,mul_zero,zero_add,add_zero,star_zero,norm_zero,zero_pow (by decide : 2≠0)]
    rw [norm_inv,inv_pow,Complex.ofReal_inv]
    simp only [Complex.star_def,map_inv₀]
    have hq : ((‖b‖^2:ℝ):ℂ)=b*star b := by
      simpa [Complex.normSq_eq_norm_sq,Complex.star_def] using (Complex.mul_conj b).symm
    rw [hq]
    have hbs : star b≠0 := star_ne_zero.mpr hb
    simp only [Complex.star_def] at hbs ⊢
    field_simp

  · change v/(‖0*z+b⁻¹‖^2+‖(0:ℂ)‖^2*v^2)=Complex.normSq b*v
    simp only [zero_mul,zero_add,add_zero,norm_zero,zero_pow (by decide : 2≠0),norm_inv,inv_pow]
    rw [Complex.normSq_eq_norm_sq]
    field_simp

lemma complex_bruhat_nonzero (g : SL(2,ℂ)) (hc : g 1 0≠0) :
    g=complexTranslation (g 0 0/g 1 0)*complexDiagonal (g 1 0)⁻¹ (inv_ne_zero hc)*
      complexWeyl*complexTranslation (g 1 1/g 1 0) := by
  have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using g.property
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) ℂ) =
    (complexTranslation (g 0 0 / g 1 0) : Matrix (Fin 2) (Fin 2) ℂ) *
    (complexDiagonal (g 1 0)⁻¹ (inv_ne_zero hc) : Matrix (Fin 2) (Fin 2) ℂ) *
    (complexWeyl : Matrix (Fin 2) (Fin 2) ℂ) *
    (complexTranslation (g 1 1 / g 1 0) : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation,complexDiagonal,complexWeyl,Matrix.mul_apply,Fin.sum_univ_two,hc] <;>
      field_simp ; linear_combination -hd

lemma complex_bruhat_zero (g : SL(2,ℂ)) (hc : g 1 0=0) :
    ∃ha : g 0 0≠0,g=complexDiagonal (g 0 0) ha*complexTranslation (g 0 1/g 0 0) := by
  have hd : g 0 0*g 1 1=1 := by simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using g.property
  have ha : g 0 0≠0 := by intro h; simp [h] at hd
  refine ⟨ha,?_⟩
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) ℂ) =
    (complexDiagonal (g 0 0) ha : Matrix (Fin 2) (Fin 2) ℂ) *
    (complexTranslation (g 0 1 / g 0 0) : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation,complexDiagonal,Matrix.mul_apply,Fin.sum_univ_two,hc] <;>
      field_simp ; linear_combination hd

def euclideanHorizontalTranslation (b : ℂ) : EuclideanSpatial := WithLp.toLp 2 ![b.re,b.im,0]

lemma complexTranslation_preserves_hyperbolicVolume (b : ℂ) :
    Measure.map (fun w => complexTranslation b • w) hyperbolicVolume=hyperbolicVolume := by
  apply hyperbolicVolume_map_of_coordinate_action (complexTranslation b)
    (fun p => p+euclideanHorizontalTranslation b) (continuous_id.add continuous_const).measurable
    (translation_preserves_hyperbolicVolume _ rfl)
  intro p hp
  have hq : 0<(p+euclideanHorizontalTranslation b) 2 := by simpa [euclideanHorizontalTranslation] using hp
  rw [euclideanToHyperbolic_positive _ hq,euclideanToHyperbolic_positive _ hp,complexTranslation_action]
  apply upperPoint_congr
  · apply Complex.ext <;> simp [euclideanHorizontalTranslation]
  · simp [euclideanHorizontalTranslation]

lemma complexDiagonal_preserves_hyperbolicVolume (b : ℂ) (hb : b≠0) :
    Measure.map (fun w => complexDiagonal b hb • w) hyperbolicVolume=hyperbolicVolume := by
  apply hyperbolicVolume_map_of_coordinate_action (complexDiagonal b hb)
    (euclideanComplexDilation b) (euclideanComplexDilation b).continuous.measurable
    (euclideanComplexDilation_preserves_hyperbolicVolume b hb)
  intro p hp
  obtain ⟨h0,h1,h2⟩ := euclideanComplexDilation_apply b p
  have hq : 0<(euclideanComplexDilation b p) 2 := by rw [h2]; exact mul_pos (Complex.normSq_pos.mpr hb) hp
  rw [euclideanToHyperbolic_positive _ hq,euclideanToHyperbolic_positive _ hp,complexDiagonal_action]
  apply upperPoint_congr
  · rw [h0,h1]
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] ; ring
  · exact h2

lemma euclidean_complex_norm_sq (p : EuclideanSpatial) :
    ‖(p 0:ℂ)+Complex.I*(p 1:ℂ)‖^2+(p 2)^2=‖p‖^2 := by
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_three,sq]

def euclideanWeylAction (p : EuclideanSpatial) : EuclideanSpatial :=
  euclideanWeylReflection (euclideanInversion p)

lemma euclideanWeylAction_measurable : Measurable euclideanWeylAction :=
  euclideanWeylReflection.continuous.measurable.comp euclideanInversion_measurable

lemma euclideanWeylAction_preserves_hyperbolicVolume :
    Measure.map euclideanWeylAction hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  rw [show euclideanWeylAction=euclideanWeylReflection ∘ euclideanInversion from rfl,
    ←Measure.map_map euclideanWeylReflection.continuous.measurable euclideanInversion_measurable,
    euclideanInversion_preserves_hyperbolicVolume,euclideanWeylReflection_preserves_hyperbolicVolume]

lemma euclideanWeylAction_apply (p : EuclideanSpatial) :
    euclideanWeylAction p 0= -((1/‖p‖)^2*p 0) ∧
      euclideanWeylAction p 1=(1/‖p‖)^2*p 1 ∧
      euclideanWeylAction p 2=(1/‖p‖)^2*p 2 := by
  simpa [euclideanWeylAction,euclideanInversion_apply] using
    euclideanWeylReflection_apply (euclideanInversion p)

lemma complexWeyl_preserves_hyperbolicVolume :
    Measure.map (fun w => complexWeyl • w) hyperbolicVolume=hyperbolicVolume := by
  apply hyperbolicVolume_map_of_coordinate_action complexWeyl euclideanWeylAction
    euclideanWeylAction_measurable euclideanWeylAction_preserves_hyperbolicVolume
  intro p hp
  have hn : ‖p‖≠0 := norm_ne_zero_iff.mpr (euclideanUpperHalf_ne_zero p hp)
  have hnc : (‖p‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hn
  obtain ⟨h0,h1,h2⟩ := euclideanWeylAction_apply p
  have hq : 0<euclideanWeylAction p 2 := by
    rw [h2]
    exact mul_pos (sq_pos_of_ne_zero (one_div_ne_zero hn)) hp
  rw [euclideanToHyperbolic_positive _ hq,euclideanToHyperbolic_positive _ hp,complexWeyl_action]
  apply upperPoint_congr
  · rw [h0,h1,euclidean_complex_norm_sq]
    simp only [Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_div,
      Complex.ofReal_one,Complex.star_def,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
    field_simp
    ; ring
  · rw [h2,euclidean_complex_norm_sq]
    field_simp

lemma hyperbolicVolume_invariant_mul (g h : SL(2,ℂ))
    (hg : Measure.map (fun w => g • w) hyperbolicVolume=hyperbolicVolume)
    (hh : Measure.map (fun w => h • w) hyperbolicVolume=hyperbolicVolume) :
    Measure.map (fun w => (g*h) • w) hyperbolicVolume=hyperbolicVolume := by
  rw [show (fun w : HyperbolicSpace => (g*h) • w)=(fun w => g • w) ∘ (fun w => h • w) by
    funext w; exact mul_smul g h w,
    ←Measure.map_map (continuous_hyperbolic_action g).measurable (continuous_hyperbolic_action h).measurable,
    hh,hg]

theorem hyperbolicVolume_invariant (g : SL(2,ℂ)) :
    Measure.map (fun w => g • w) hyperbolicVolume=hyperbolicVolume := by
  by_cases hc : g 1 0=0
  · obtain ⟨ha,hg⟩ := complex_bruhat_zero g hc
    rw [hg]
    exact hyperbolicVolume_invariant_mul _ _ (complexDiagonal_preserves_hyperbolicVolume _ ha)
      (complexTranslation_preserves_hyperbolicVolume _)
  · rw [complex_bruhat_nonzero g hc]
    exact hyperbolicVolume_invariant_mul _ _
      (hyperbolicVolume_invariant_mul _ _
        (hyperbolicVolume_invariant_mul _ _ (complexTranslation_preserves_hyperbolicVolume _)
          (complexDiagonal_preserves_hyperbolicVolume _ (inv_ne_zero hc)))
        complexWeyl_preserves_hyperbolicVolume)
      (complexTranslation_preserves_hyperbolicVolume _)

end CubicEisenstein

open scoped BigOperators Classical

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace CanonicalQuadraticSieve

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

def poissonUnitBudget
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N : ℝ) (W : 𝓢(ℝ,ℂ)) : List ℝ :=
  [(IdealMobiusDivisorSum.idealDivisors G).card,
   (columnDyadicLength K+1:ℕ), (columnDyadicLength N+1:ℕ),
   256*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2,
   divisorExponentConstant hexp deltaLoss hδ*((2*K)*N)^deltaLoss,
   ‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖,
   ‖quadraticTransformedSquareProfile W 0‖,
   dualMiddleDecayConstant (quadraticTransformedSquareProfile W),
   ‖paperRadialFourier (quadraticSquareProfile W) 0‖,
   originalMiddleDecayConstant (quadraticSquareProfile W),
   nonzeroLatticeEnvelopeConstant,
   supportConstant ε hε*(N*N)^ε*(CD*sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)),
   supportConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε*(CS*sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)),
   CT*sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W,
   supportConstant ε hε*N^ε*CP*(K*N)^deltaLoss]

end CanonicalQuadraticSieve

open scoped BigOperators Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

namespace CubicEisenstein

def matrixGram (g : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  (g : Matrix (Fin 2) (Fin 2) ℂ)*star (g : Matrix (Fin 2) (Fin 2) ℂ)

lemma matrixGram_right_unitary (g k : SL(2,ℂ)) (hk : k∈compactSubgroup) :
    matrixGram (g*k)=matrixGram g := by
  have hku : (k : Matrix (Fin 2) (Fin 2) ℂ)*star (k : Matrix (Fin 2) (Fin 2) ℂ)=1 :=
    Matrix.mem_unitaryGroup_iff.mp hk
  unfold matrixGram
  simp only [Matrix.SpecialLinearGroup.coe_mul,star_mul]
  calc
    _ = (g : Matrix (Fin 2) (Fin 2) ℂ)*
        ((k : Matrix (Fin 2) (Fin 2) ℂ)*star (k : Matrix (Fin 2) (Fin 2) ℂ))*
        star (g : Matrix (Fin 2) (Fin 2) ℂ) := by noncomm_ring
    _ = _ := by rw [hku]; simp

def hyperbolicGram : HyperbolicSpace → Matrix (Fin 2) (Fin 2) ℂ :=
  Quotient.lift matrixGram (by
    intro g h hgh
    have hk : g⁻¹*h∈compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h=g*(g⁻¹*h) := by group
    rw [hh]
    exact (matrixGram_right_unitary g (g⁻¹*h) hk).symm)

lemma hyperbolicGram_continuous : Continuous hyperbolicGram := by
  apply Continuous.quotient_lift
  exact continuous_complexSL_coe.mul continuous_complexSL_coe.star

lemma hyperbolicGram_injective : Function.Injective hyperbolicGram := by
  intro w w' hw
  induction w using Quotient.inductionOn with | _ g =>
    induction w' using Quotient.inductionOn with | _ h =>
      change matrixGram g=matrixGram h at hw
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      change (g⁻¹*h:SL(2,ℂ))∈compactSubgroup
      apply Matrix.mem_unitaryGroup_iff.mpr
      have hgi : ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*
          (g:Matrix (Fin 2) (Fin 2) ℂ)=1 :=
        congrArg (fun x : SL(2,ℂ) => (x:Matrix (Fin 2) (Fin 2) ℂ)) (inv_mul_cancel g)
      have hgis : star (g:Matrix (Fin 2) (Fin 2) ℂ)*
          star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)=1 := by
        simpa only [star_mul,star_one] using congrArg star hgi
      simp only [Matrix.SpecialLinearGroup.coe_mul,star_mul]
      calc
        _ = ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*matrixGram h*
            star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ) := by unfold matrixGram; noncomm_ring
        _ = ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*matrixGram g*
            star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ) := by rw [hw]
        _ = (((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*(g:Matrix (Fin 2) (Fin 2) ℂ))*
            (star (g:Matrix (Fin 2) (Fin 2) ℂ)*star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)) := by
          unfold matrixGram
          noncomm_ring
        _ = 1 := by rw [hgi,hgis]; simp

instance hyperbolicT2Space : T2Space HyperbolicSpace :=
  T2Space.of_injective_continuous hyperbolicGram_injective hyperbolicGram_continuous

def complexMatrixRow (g : SL(2,ℂ)) (i : Fin 2) : Fin 2 → ℂ := fun j => g i j

lemma complexMatrixRow_mul (g h : SL(2,ℂ)) (i : Fin 2) :
    complexMatrixRow (g*h) i=rowOperator h (complexMatrixRow g i) := by
  funext j
  simp only [complexMatrixRow,rowOperator_apply,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Matrix.vecMul,dotProduct]

def matrixFrobenius (g : SL(2,ℂ)) : ℝ :=
  rowEnergy (complexMatrixRow g 0)+rowEnergy (complexMatrixRow g 1)

lemma matrixFrobenius_right_unitary (g k : SL(2,ℂ)) (hk : k∈compactSubgroup) :
    matrixFrobenius (g*k)=matrixFrobenius g := by
  simp only [matrixFrobenius,complexMatrixRow_mul,rowEnergy_unitary k hk]

def hyperbolicFrobenius : HyperbolicSpace → ℝ :=
  Quotient.lift matrixFrobenius (by
    intro g h hgh
    have hk : g⁻¹*h∈compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h=g*(g⁻¹*h) := by group
    rw [hh]
    exact (matrixFrobenius_right_unitary g (g⁻¹*h) hk).symm)

lemma matrixFrobenius_continuous : Continuous matrixFrobenius := by
  have he (i j : Fin 2) : Continuous (fun g : SL(2,ℂ) => g i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_complexSL_coe)
  unfold matrixFrobenius rowEnergy complexMatrixRow
  exact ((he 0 0).norm.pow 2 |>.add ((he 0 1).norm.pow 2)).add
    ((he 1 0).norm.pow 2 |>.add ((he 1 1).norm.pow 2))

lemma hyperbolicFrobenius_continuous : Continuous hyperbolicFrobenius :=
  matrixFrobenius_continuous.quotient_lift _

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

def poissonPrimitiveConstants
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    {α : ℝ} (hexp : HasSieveExponent α) (η : ℝ) (hη : 0<η)
    (D : ℝ) (W : 𝓢(ℝ,ℂ)) : List ℝ :=
  [divisorConstant η hη, 2+1/(η*Real.log 2), 256,
   supportConstant η hη, divisorExponentConstant hexp η hη,
   ‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖,
   ‖quadraticTransformedSquareProfile W 0‖,
   dualMiddleDecayConstant (quadraticTransformedSquareProfile W),
   ‖paperRadialFourier (quadraticSquareProfile W) 0‖,
   originalMiddleDecayConstant (quadraticSquareProfile W),
   nonzeroLatticeEnvelopeConstant, CD, CS, CT, CP,
   sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W),
   sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W),
   sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W, D^η]

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

def poissonShape (M X α : ℝ) : ℝ := M+X+X^(2*α-1)*M^(1-α)
def poissonShapeConstant (B C1 : ℝ) : ℝ := 2+4*C1^3+B^2+C1

end CanonicalQuadraticSieve

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel UniqueFactorizationMonoid

def rowPowerfulPart (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => 2≤(normalizedFactors I).count P)).prod

def rowSimplePart (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => ¬2≤(normalizedFactors I).count P)).prod

theorem rowSimplePart_ne_zero (I : Ideal O) : rowSimplePart I≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem normalizedFactors_rowPowerfulPart (I : Ideal O) :
    normalizedFactors (rowPowerfulPart I)=
      (normalizedFactors I).filter (fun P => 2≤(normalizedFactors I).count P) :=
  normalizedFactors_prod_of_prime (fun P hP => prime_of_normalized_factor P (Multiset.mem_filter.mp hP).1)

theorem normalizedFactors_rowSimplePart (I : Ideal O) :
    normalizedFactors (rowSimplePart I)=
      (normalizedFactors I).filter (fun P => ¬2≤(normalizedFactors I).count P) :=
  normalizedFactors_prod_of_prime (fun P hP => prime_of_normalized_factor P (Multiset.mem_filter.mp hP).1)

theorem rowSimplePart_squarefree (I : Ideal O) : Squarefree (rowSimplePart I) := by
  apply (squarefree_iff_nodup_normalizedFactors (rowSimplePart_ne_zero I)).mpr
  rw [normalizedFactors_rowSimplePart]
  apply Multiset.nodup_iff_count_le_one.mpr
  intro P
  rw [Multiset.count_filter]
  split_ifs <;> omega

theorem row_powerful_simple_product (I : Ideal O) (hI : I≠0) :
    rowPowerfulPart I*rowSimplePart I=I := by
  rw [rowPowerfulPart,rowSimplePart,←Multiset.prod_add,Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

end

open ActualEisensteinCubic CanonicalQuadraticSieve UniqueFactorizationMonoid

def squarefreeMaskPart (I R : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => P∣R)).prod

def squarefreeResidualPart (I R : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => ¬P∣R)).prod

theorem squarefreeResidualPart_ne_zero (I R : Ideal O) : squarefreeResidualPart I R≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem normalizedFactors_squarefreeMaskPart (I R : Ideal O) :
    normalizedFactors (squarefreeMaskPart I R)=(normalizedFactors I).filter (fun P => P∣R) :=
  normalizedFactors_prod_of_prime (fun P hP => prime_of_normalized_factor P (Multiset.mem_filter.mp hP).1)

theorem normalizedFactors_squarefreeResidualPart (I R : Ideal O) :
    normalizedFactors (squarefreeResidualPart I R)=(normalizedFactors I).filter (fun P => ¬P∣R) :=
  normalizedFactors_prod_of_prime (fun P hP => prime_of_normalized_factor P (Multiset.mem_filter.mp hP).1)

theorem squarefreeResidualPart_squarefree (I R : Ideal O) (hI : Squarefree I) : Squarefree (squarefreeResidualPart I R) := by
  apply (squarefree_iff_nodup_normalizedFactors (squarefreeResidualPart_ne_zero I R)).mpr
  rw [normalizedFactors_squarefreeResidualPart]
  exact ((squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI).filter _

theorem squarefree_mask_residual_product (I R : Ideal O) (hI : I≠0) :
    squarefreeMaskPart I R*squarefreeResidualPart I R=I := by
  rw [squarefreeMaskPart,squarefreeResidualPart,←Multiset.prod_add,Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem squarefreeResidualPart_coprime (I R : Ideal O) : IsCoprime (squarefreeResidualPart I R) R := by
  apply ideals_coprime_of_relprime
  apply (isRelPrime_iff_no_prime_factors (squarefreeResidualPart_ne_zero I R)).mpr
  intro P hp hr hP
  have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero I R)).mpr ⟨hP,hp⟩
  rw [normalizedFactors_squarefreeResidualPart] at hm
  exact (Multiset.mem_filter.mp hm).2 hr

def rowMaskPart (I R : Ideal O) : Ideal O := squarefreeMaskPart (rowSimplePart I) R
def rowResidualPart (I R : Ideal O) : Ideal O := squarefreeResidualPart (rowSimplePart I) R

theorem row_powerful_mask_residual_product (I R : Ideal O) (hI : I≠0) :
    rowPowerfulPart I*rowMaskPart I R*rowResidualPart I R=I := by
  rw [mul_assoc,rowMaskPart,rowResidualPart,squarefree_mask_residual_product _ _ (rowSimplePart_ne_zero I),
    row_powerful_simple_product I hI]

theorem rowResidualPart_squarefree (I R : Ideal O) : Squarefree (rowResidualPart I R) :=
  squarefreeResidualPart_squarefree _ _ (rowSimplePart_squarefree I)

theorem rowResidualPart_admissible (I R : Ideal O) (hbad : ∀P∈fixedBadPrimes,P∣R) :
    Admissible (rowResidualPart I R) :=
  admissible_of_squarefree_coprime_bad _ R (rowResidualPart_squarefree I R)
    (squarefreeResidualPart_coprime (rowSimplePart I) R) hbad

theorem rowResidualPart_prime_exponent (I R P : Ideal O)
    (hP : P∈normalizedFactors (rowResidualPart I R)) :
    P∈normalizedFactors I ∧ (normalizedFactors I).count P=1 ∧ ¬P∣R := by
  rw [rowResidualPart,normalizedFactors_squarefreeResidualPart] at hP
  obtain ⟨hs,hr⟩ := Multiset.mem_filter.mp hP
  rw [normalizedFactors_rowSimplePart] at hs
  obtain ⟨hi,hcount⟩ := Multiset.mem_filter.mp hs
  exact ⟨hi,by have hp := Multiset.count_pos.mpr hi; omega,hr⟩

end CompletedGauss

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace CubicEisenstein

section
open Filter MeasureTheory LineDeriv
open scoped BigOperators Classical Topology SchwartzMap LineDeriv

abbrev EuclideanL2 := Lp ℂ 2 (volume : Measure EuclideanSpatial)
abbrev EuclideanGradientL2 := PiLp 2 (fun _ : Fin 3 => EuclideanL2)
abbrev EuclideanDistributions := TemperedDistribution EuclideanSpatial ℂ

def euclideanCoordinateVector (j : Fin 3) : EuclideanSpatial := WithLp.toLp 2 (Pi.single j 1)
def euclideanL2Distribution : EuclideanL2 →L[ℂ] EuclideanDistributions :=
  Lp.toTemperedDistributionCLM ℂ volume 2

lemma euclideanL2Distribution_injective : Function.Injective euclideanL2Distribution := by
  apply LinearMap.ker_eq_bot.mp
  exact Lp.ker_toTemperedDistributionCLM_eq_bot

def euclideanGradientEquations : EuclideanL2 × EuclideanGradientL2 →L[ℂ]
    (Fin 3 → EuclideanDistributions) :=
  ContinuousLinearMap.pi (fun j =>
    (lineDerivOpCLM ℂ EuclideanDistributions (euclideanCoordinateVector j)).comp
      (euclideanL2Distribution.comp (ContinuousLinearMap.fst ℂ EuclideanL2 EuclideanGradientL2))-
    euclideanL2Distribution.comp ((PiLp.proj 2 (fun _ : Fin 3 => EuclideanL2) j).comp
      (ContinuousLinearMap.snd ℂ EuclideanL2 EuclideanGradientL2)))

def euclideanWeakGradientGraph : Submodule ℂ (EuclideanL2 × EuclideanGradientL2) :=
  euclideanGradientEquations.ker

lemma mem_euclideanWeakGradientGraph (f : EuclideanL2) (g : EuclideanGradientL2) :
    (f,g)∈euclideanWeakGradientGraph ↔ ∀j,
      ∂_{euclideanCoordinateVector j} (euclideanL2Distribution f)=euclideanL2Distribution (g j) := by
  change (fun j => ∂_{euclideanCoordinateVector j} (euclideanL2Distribution f)-
    euclideanL2Distribution (g j))=0 ↔ _
  simp only [funext_iff,Pi.zero_apply,sub_eq_zero]

lemma euclideanWeakGradientGraph_unique (x : EuclideanL2 × EuclideanGradientL2)
    (hx : x∈euclideanWeakGradientGraph) (hzero : x.1=0) : x.2=0 := by
  have hh := (mem_euclideanWeakGradientGraph x.1 x.2).mp hx
  apply (WithLp.equiv 2 (Fin 3 → EuclideanL2)).injective
  funext j
  change x.2 j=(0:EuclideanL2)
  apply euclideanL2Distribution_injective
  simpa only [hzero,map_zero,lineDerivOp_zero,WithLp.ofLp_zero,Pi.zero_apply] using (hh j).symm

lemma schwartz_mem_euclideanWeakGradientGraph (f : 𝓢(EuclideanSpatial,ℂ)) :
    (f.toLp 2 volume,WithLp.toLp 2 (fun j => (∂_{euclideanCoordinateVector j} f).toLp 2 volume))∈euclideanWeakGradientGraph := by
  apply (mem_euclideanWeakGradientGraph _ _).mpr
  intro j
  dsimp only [euclideanL2Distribution]
  simp only [Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistribution_toLp_eq]
  exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq («μ» := volume) f _

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology SchwartzMap LineDeriv

abbrev EuclideanH1Ambient := WithLp 2 (EuclideanL2 × EuclideanGradientL2)

def euclideanH1Submodule : Submodule ℂ EuclideanH1Ambient :=
  euclideanWeakGradientGraph.comap (WithLp.linearEquiv 2 ℂ (EuclideanL2 × EuclideanGradientL2)).toLinearMap

lemma euclideanH1Submodule_isClosed : IsClosed (euclideanH1Submodule : Set EuclideanH1Ambient) := by
  have hg : IsClosed (euclideanWeakGradientGraph : Set (EuclideanL2 × EuclideanGradientL2)) :=
    euclideanGradientEquations.isClosed_ker
  exact hg.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).continuous

abbrev EuclideanH1 := euclideanH1Submodule

instance euclideanH1Complete : CompleteSpace EuclideanH1 :=
  euclideanH1Submodule_isClosed.completeSpace_coe

def euclideanH1Embedding : EuclideanH1 →L[ℂ] EuclideanL2 :=
  (ContinuousLinearMap.fst ℂ EuclideanL2 EuclideanGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).toContinuousLinearMap.comp
      euclideanH1Submodule.subtypeL)

def euclideanH1Gradient : EuclideanH1 →L[ℂ] EuclideanGradientL2 :=
  (ContinuousLinearMap.snd ℂ EuclideanL2 EuclideanGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).toContinuousLinearMap.comp
      euclideanH1Submodule.subtypeL)

lemma euclideanH1Embedding_eq_zero (u : EuclideanH1) (hu : euclideanH1Embedding u=0) : u=0 := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (EuclideanL2 × EuclideanGradientL2)).injective
  apply Prod.ext
  · exact hu
  · exact euclideanWeakGradientGraph_unique u.1.ofLp u.2 hu

lemma euclideanH1Embedding_injective : Function.Injective euclideanH1Embedding := by
  intro u v huv
  apply sub_eq_zero.mp
  apply euclideanH1Embedding_eq_zero
  rw [map_sub,huv,sub_self]

lemma euclideanH1_norm_sq (u : EuclideanH1) :
    ‖u‖^2=‖euclideanH1Embedding u‖^2+‖euclideanH1Gradient u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.1

end CubicEisenstein

open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CompletedGauss FirstCauchyArithmetic ShortDraftHeckeBridge

def normCharacter {q : ℕ} (χ : DirichletCharacter ℂ q) : O→*ℂ where
  toFun a := χ (Ideal.absNorm (Ideal.span {a}))
  map_one' := by simp
  map_mul' a b := by
    rw [←Ideal.span_singleton_mul_span_singleton]
    simp

def selectedIdealTest (F : Finset (Ideal O)) (W : ℕ→ℂ) (S : Finset (primePool F)) : ℂ :=
  if (∏i∈S,i.val)∈F then W (Ideal.absNorm (∏i∈S,i.val)) else 0

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open MeasureTheory
open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

def rowFamilyEnergy (labels : Finset (Ideal ActualEisensteinCubic.O)) (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ) (K : ℝ) : ℝ :=
  (∑ I ∈ labels, nonzeroRowMajorantSum (P I) K).re

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

end CanonicalRowCompletion

open scoped BigOperators Classical

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

section
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

abbrev CompletedMellinIndex := NonzeroIdeal×NonzeroIdeal

def completedMellinLength (p : CompletedMellinIndex) : ℝ :=
  (Ideal.absNorm p.1.1:ℝ)*(Ideal.absNorm p.2.1:ℝ)^3

def completedMellinCoefficient (Ψ : ActualEisensteinCubic.O→*ℂ) (p : CompletedMellinIndex) : ℂ :=
  columnWeight Ψ p.1.1/(Real.sqrt (Ideal.absNorm p.1.1:ℝ):ℂ)*cubeWeight Ψ p.2.1

lemma nonzeroIdeal_norm_pos (I : NonzeroIdeal) : 0<(Ideal.absNorm I.1:ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (fun h=>I.2 (Ideal.absNorm_eq_zero_iff.mp h))

def completedDirichletSeries (Ψ : ActualEisensteinCubic.O→*ℂ) (s : ℂ) : ℂ :=
  ∑'p : CompletedMellinIndex,completedMellinCoefficient Ψ p*
    (completedMellinLength p:ℂ)^(1/2-s)

end

open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

end CompletedGauss

open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

namespace CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def dualIdealDyad (j : ℕ) : Finset (Ideal Eis) :=
  (ConcretePrimeRowBridge.idealsUpTo (2^j)).filter
    (fun I => Nat.clog 2 (Ideal.absNorm I)=j)

lemma mem_dualIdealDyad (I : Ideal Eis) (j : ℕ) :
    I∈dualIdealDyad j ↔ I≠0 ∧ Nat.clog 2 (Ideal.absNorm I)=j := by
  simp only [dualIdealDyad,Finset.mem_filter,ConcretePrimeRowBridge.mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hI,_⟩,hj⟩
    exact ⟨fun h => by simp [h] at hI, hj⟩
  · rintro ⟨hI,hj⟩
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI),?_⟩,hj⟩
    simpa only [hj] using Nat.le_pow_clog (by norm_num : 1<2) (Ideal.absNorm I)

abbrev NonzeroDualIdeal := {I : Ideal Eis // I≠0}

def dualDyadicIndexEquiv :
    (ℕ×NonzeroDualIdeal×NonzeroDualIdeal) ≃
      (Σ i : ℕ×ℕ×ℕ, (dualIdealDyad i.2.2)×(dualIdealDyad i.2.1)) where
  toFun x := ⟨(x.1,Nat.clog 2 (Ideal.absNorm x.2.2.val),Nat.clog 2 (Ideal.absNorm x.2.1.val)),
    ⟨⟨x.2.1.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.1.property,rfl⟩⟩,
      ⟨x.2.2.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.2.property,rfl⟩⟩⟩⟩
  invFun x := ⟨x.1.1,⟨x.2.1.val,((mem_dualIdealDyad _ _).mp x.2.1.property).1⟩,
    ⟨x.2.2.val,((mem_dualIdealDyad _ _).mp x.2.2.property).1⟩⟩
  left_inv x := by cases x; rfl
  right_inv x := by
    rcases x with ⟨⟨m,j,k⟩,⟨⟨I,hI⟩,⟨J,hJ⟩⟩⟩
    have hi:=((mem_dualIdealDyad I k).mp hI).2
    have hj:=((mem_dualIdealDyad J j).mp hJ).2
    dsimp only
    subst k
    subst j
    rfl

end CompletedGauss

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace CompletedGauss
open Filter MeasureTheory
open scoped Classical BigOperators Topology

section
open CubicEisenstein

def completedBesselProfile (Ψ : ActualEisensteinCubic.O→*ℂ) (q : ℝ) : ℝ→ℂ :=
  radialBesselProfile completedMellinLength (completedMellinCoefficient Ψ) q

def besselMellinFactor (q : ℝ) (s : ℂ) : ℂ :=
  ((2:ℂ)^(2*s-1)*Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))/
    ((4*Real.pi*q:ℝ):ℂ)^(2*s+1)

def inverseBesselMellinFactor (q : ℝ) (s : ℂ) : ℂ :=
  ((4*Real.pi*q:ℝ):ℂ)^(2*s+1)*(2:ℂ)^(1-2*s)*
    (Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))⁻¹

end

def continuedBesselDirichlet (F : ℝ→ℂ) (q : ℝ) (s : ℂ) : ℂ :=
  inverseBesselMellinFactor q s*mellin F (2*s)

end CompletedGauss

open scoped BigOperators Classical

namespace CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

def besselSmoothingIntegrand (F : ℝ→ℂ) (q : ℝ) (V : ℝ→ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  mellin V (s-1/2)*(X:ℂ)^(s-1/2)*continuedBesselDirichlet F q s

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CompletedGauss
open CubicEisenstein

def besselReflectionFactor (q d : ℝ) (s : ℂ) : ℂ :=
  ((4*Real.pi*q:ℝ):ℂ)^(2*s+1)*(2:ℂ)^(2-4*s)/
    ((4*Real.pi*d:ℝ):ℂ)^(3-2*s)

end CompletedGauss

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace CompletedGauss
open scoped BigOperators Classical ContDiff
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "Eis" => ActualEisensteinCubic.O

def rawDualKernelTerm (V : ℝ→ℂ) (scale ρ q : ℝ)
    (β : ℕ→Ideal Eis→Ideal Eis→ℂ) (x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal) : ℂ :=
  β x.1 x.2.1.val x.2.2.val * CubicReflectionKernel.paperKernel V
    (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3)

end

open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance ramifiedFrequencyUnitsFintype : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def firstImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => goodPart (firstPart (Ideal.span {z})))
def secondImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => goodPart (secondPart (Ideal.span {z})))
def cubeImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => cubePart (Ideal.span {z}))

def sourceFactor (R : Finset O)
    (d : Oˣ × CanonicalQuadraticSieve.fixedBadPrimes.powerset ×
      CanonicalQuadraticSieve.fixedBadPrimes.powerset × cubeImage R) : O :=
  d.1.val * idealGenerator d.2.2.2.val ^ 3 *
    (idealGenerator (∏ P ∈ d.2.1.val, P) * idealGenerator (∏ P ∈ d.2.2.1.val, P) ^ 2)

end
end SevenEighths.CubicSieve

end OAI
end

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def extractionLabel (M : ℝ) (z : O) :
    Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) :=
  (CanonicalQuadraticSieve.divisorDyadicLabel M (firstPart (Ideal.span {z})),
   CanonicalQuadraticSieve.divisorDyadicLabel M (secondPart (Ideal.span {z})))

def extractionBin (R : Finset O) (M : ℝ)
    (j : Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1)) : Finset O :=
  R.filter (fun z => extractionLabel M z = j)

end
end SevenEighths.CubicSieve

end OAI
end

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve FiniteSieveRestriction
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicColumnLabel {n : Type*} (cols : n → Ideal O) (N : ℝ) (j : n) :
    Fin (columnDyadicLength N + 1) := divisorDyadicLabel N (cols j)

abbrev CubicColumnShell {n : Type*} (cols : n → Ideal O) (N : ℝ)
    (l : Fin (columnDyadicLength N + 1)) := {j : n // cubicColumnLabel cols N j = l}

end
end SevenEighths.CubicSieve

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def childFrequencyBall (a : Eis) (R : ℝ) : Finset Eis :=
  (secondFrequencyCutoff (‖eisEmbedding a‖^2) R).filter
    (fun k => ‖eisEmbedding (a*k)‖^2 ≤ R)

def nonzeroChildFrequencyBall (a : Eis) (R : ℝ) : Finset Eis :=
  (childFrequencyBall a R).erase 0

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

def outsideCanonicalMarkedRow {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (Ψ : O →* ℂ) (m f z : O) (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m f z slots lists a W X

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def hybridSquarePool (S : Finset (Ideal Eis × Ideal Eis)) : Finset (Ideal Eis) :=
  (hybridColumnSupport S).image HybridColumnData.square

def hybridCommonBlock (S : Finset (Ideal Eis × Ideal Eis)) (N : ℝ)
    (i : Fin (columnDyadicLength N + 1)) (t : Ideal Eis) : Finset HybridColumnData :=
  (hybridColumnSupport S).filter fun d =>
    d.square = t ∧ divisorDyadicLabel N d.common = i

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def firstRetainedSource (p : ι→O) (labels : Finset (Ideal O)) (b : CubeCoordinates ι) (Y : ℝ) :
    Finset (Ideal O×O) :=
  labels.biUnion (fun f=> (nonzeroChildFrequencyBall
    (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) Y).image
      (fun h=>(f,h)))

variable (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι κ:Type*} [DecidableEq ι] [DecidableEq κ]

def firstGlobalRetainedSource (p:ι→Eis) (outer:Finset κ)
    (labels:κ→Finset (Ideal Eis)) (cube:κ→CubeCoordinates ι) (Y:ℝ):
    Finset (Σ _ : κ,Ideal Eis×Eis):=
  outer.sigma (fun k=>firstRetainedSource p (labels k) (cube k) Y)

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem fullIdealWeight_continuous (I : Ideal O) : Continuous (fun t => fullIdealWeight t I) := by
  by_cases hI : I = 0
  · simp only [hI, fullIdealWeight]
    exact continuous_const
  · have hn : (Ideal.absNorm I : ℂ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_ne_zero_iff I).mpr
        (Ring.HasFiniteQuotients.finiteQuotient hI)
    simp only [fullIdealWeight, if_neg hI]
    exact continuous_id.neg.const_cpow (Or.inl hn)

def rowMajorant (σ : ℝ) (p : Ideal O × Ideal O) : ℝ :=
  2 * (‖fullIdealWeight (σ : ℂ) p.1‖ * ‖fullIdealWeight (3 * (σ : ℂ)) p.2‖)

end SevenEighths.ProbeRow
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma supportedIdealProduct_injective (C : SupportedIdeal) : Function.Injective (supportedIdealProduct C) := by
  intro I J h
  apply Subtype.ext
  exact mul_left_cancel₀ C.property.1 (congrArg Subtype.val h)

def commonPool (F : Finset SupportedIdeal) : Finset SupportedIdeal :=
  (F×ˢF).image (fun p=>gcdCommon p.1 p.2)
def commonColumns (F : Finset SupportedIdeal) (C : SupportedIdeal) : Finset SupportedIdeal :=
  F.preimage (supportedIdealProduct C) (supportedIdealProduct_injective C).injOn

def commonTriples (F : Finset SupportedIdeal) : Finset ((_C : SupportedIdeal)×(SupportedIdeal×SupportedIdeal)) :=
  (commonPool F).sigma (fun C=>(commonColumns F C×ˢcommonColumns F C).filter (fun p=>IsCoprime p.1.val p.2.val))

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeReciprocalBound
open HeckeFamily

def bound (σ : ℝ) : ℝ :=
  ∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight (σ : ℂ) I‖

end SevenEighths.HeckeReciprocalBound

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ConcreteTraceCRT ActualEisensteinCubic
local notation "O" => HeckeFamily.O

lemma freeRow_count (R : Finset FreeRow) (H : ℝ) (hH : 1≤H)
    (hR : ∀u∈R,((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤H) :
    (R.card:ℝ)≤128*H := by
  have hc := DescentFiberCost.finite_element_count_real (R.image Subtype.val) H hH (by
    intro a ha
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ha
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact hR u hu)
  rw [Finset.card_image_of_injective R Subtype.val_injective] at hc
  exact hc

end SevenEighths.ProbeHighRowFamily
end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

abbrev RawTailIndex := ℕ×NonzeroDualIdeal×NonzeroDualIdeal

def rawTailWeight (q : ℝ) (x : RawTailIndex) : ℝ :=
  ((q^6)⁻¹)^x.1*((Ideal.absNorm x.2.1.val:ℝ)^2)⁻¹*((Ideal.absNorm x.2.2.val:ℝ)^6)⁻¹

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def rawDyadicLabel (x : RawTailIndex) : ℕ×ℕ×ℕ :=
  (x.1,Nat.clog 2 (Ideal.absNorm x.2.2.val),Nat.clog 2 (Ideal.absNorm x.2.1.val))

def rawDyadicCenter (scale : ℝ) (i : ℕ×ℕ×ℕ) : ℝ :=
  scale*(ramifiedScale 1 completedRamifiedStep i.1)^3*(2:ℝ)^i.2.2*((2:ℝ)^i.2.1)^3

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section

def retainedDyadicBox (scale B : ℝ) : Finset (ℕ×ℕ×ℕ) :=
  let n := columnDyadicLength (max 1 (B/scale))
  (Finset.range (n+1)) ×ˢ ((Finset.range (n+1)) ×ˢ (Finset.range (n+1)))

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def retainedDyads (scale B : ℝ) : Finset (ℕ×ℕ×ℕ) :=
  (retainedDyadicBox scale B).filter (fun i => rawDyadicCenter scale i≤B)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def activeTupleDyad (tuples : Finset (σ→Ideal Eis)) (H : ℝ)
    (i : Fin (columnDyadicLength H+1)) : Finset (σ→Ideal Eis) :=
  tuples.filter fun p => divisorDyadicLabel H (slotTupleProduct p)=i

end
end SevenEighths.InverseReflectedPhase

end OAI
end



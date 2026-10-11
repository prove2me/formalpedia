-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0095
-- name    : PNT_ZeroFree_433_0095
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:26:27.107125+00:00
-- url     : https://prove2.me/theorems/49f90cb9-8537-4c46-9d59-920109d18519
-- title:
--   Zero-free region foundations: QuadraticSieve.PrincipalTruncation [0095]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalTruncation
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PrincipalTruncation.lean#L80-L622

import Definitions.Def_PNT_ZeroFree_433_0094

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PrincipalTruncation.lean#L80-L622
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalTruncation
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex

def lowPrincipalIdeal (I J : Ideal O) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' A : {A : Ideal O // Supported A},
    (idealZeroMask I (primaryGenerator A.val) * idealZeroMask J (primaryGenerator A.val)) *
      W (((Ideal.absNorm A.val : ℝ) / X) ^ 2)

def lowPrincipalLattice (I J : Ideal O) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' z : O, rowCoprimeMask (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ z *
    W ((‖eisEmbedding z‖ ^ 2 / X) ^ 2)

theorem lowPrincipalLattice_eq_six_ideal (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (X : ℝ) (hX : 0 < X) :
    lowPrincipalLattice I J W X = 6 * lowPrincipalIdeal I J W X := by
  let R := fun P : gcdMaskPrimes (I * J) => P.val
  let V := quadraticSquareProfile W
  let f : O → ℂ := fun z => rowCoprimeMask R Finset.univ z * V (‖eisEmbedding z‖ ^ 2 / X)
  have hV : Summable (fun z : O => ‖V (‖eisEmbedding z‖ ^ 2 / X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest V X hX)
  have hf : Summable f := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _ hV
    intro z
    dsimp only [f]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (QuadraticUnitInvariance.rowCoprimeMask_norm_le_one R Finset.univ z)
  have h0 : f 0 = 0 := by
    dsimp only [f, R]
    rw [jointMask_zero, zero_mul]
  have hu (u : Oˣ) (z : O) : f (u.val * z) = f z := by
    dsimp only [f]
    rw [QuadraticUnitInvariance.rowCoprimeMask_unit_mul, norm_eisEmbedding_unit_mul]
  have he := tsum_unit_invariant_of_zero f hf h0 hu
  have hnorm (A : Ideal O) : ‖eisEmbedding (idealGenerator A)‖ ^ 2 = (Ideal.absNorm A : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span, span_idealGenerator]
  simp only [f, V, quadraticSquareProfile_apply, hnorm] at he
  have hid : (∑' A : NonzeroIdeal, rowCoprimeMask R Finset.univ (idealGenerator A.val) *
      W (((Ideal.absNorm A.val : ℝ) / X) ^ 2)) = lowPrincipalIdeal I J W X := by
    let F : Ideal O → ℂ := fun A => if Supported A then
      (idealZeroMask I (primaryGenerator A) * idealZeroMask J (primaryGenerator A)) *
        W (((Ideal.absNorm A : ℝ) / X) ^ 2) else 0
    calc
      _ = ∑' A : NonzeroIdeal, F A.val := by
        apply tsum_congr
        intro A
        rw [jointMask_generator I J hI hJ]
        by_cases hA : Supported A.val <;> simp [hA, F]
      _ = ∑' A : Ideal O, F A := by
        apply tsum_subtype_eq_of_support_subset
        intro A hA
          hz
        subst A
        exact hA (by simp [F, Supported])
      _ = _ := by
        calc
          _ = ∑' A : Ideal O, ({A : Ideal O | Supported A} : Set (Ideal O)).indicator
              (fun A => (idealZeroMask I (primaryGenerator A) * idealZeroMask J (primaryGenerator A)) *
                W (((Ideal.absNorm A : ℝ) / X) ^ 2)) A := by
            apply tsum_congr
            intro A
            rfl
          _ = _ := (_root_.tsum_subtype _ _).symm
  rw [hid] at he
  exact he

theorem lowPrincipalIdeal_eq_lattice (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (X : ℝ) (hX : 0 < X) :
    lowPrincipalIdeal I J W X = (6 : ℂ)⁻¹ * lowPrincipalLattice I J W X := by
  rw [lowPrincipalLattice_eq_six_ideal I J hI hJ W X hX]
  ring

theorem originalPairLow_principal_lattice
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (M K : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale) =
      ∑' B : {B : Ideal O // Admissible B}, if (Ideal.absNorm B.val : ℝ) ≤ K then
        (quadraticRow I (primaryGenerator B.val) * quadraticRow J (primaryGenerator B.val)) *
          ((6 : ℂ)⁻¹ * lowPrincipalLattice I J W (Real.sqrt (M / (Ideal.absNorm B.val : ℝ))))
      else 0 := by
  rw [originalPairLow_squarefree_tsum I J hI hJ W M K hM]
  apply tsum_congr
  intro B
  by_cases hB : (Ideal.absNorm B.val : ℝ) ≤ K
  · rw [if_pos hB, if_pos hB]
    congr 1
    have hN : 0 < (Ideal.absNorm B.val : ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => B.property.1 (Ideal.absNorm_eq_zero_iff.mp h))
    have hX : 0 < Real.sqrt (M / (Ideal.absNorm B.val : ℝ)) := Real.sqrt_pos.mpr (div_pos hM hN)
    rw [← lowPrincipalIdeal_eq_lattice I J hI hJ W _ hX]
    unfold lowPrincipalIdeal
    apply tsum_congr
    intro A
    congr 2
    rw [div_pow, Real.sq_sqrt (div_pos hM hN).le]
    field_simp
  · simp only [if_neg hB]

end
section

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson TruncatedPrincipalPoisson IdealCoprimeSieveOperator

def lowPrincipalMain (I J : Ideal O) (W : SchwartzMap ℝ ℂ) (X Z : ℝ) : ℂ :=
  (6 : ℂ)⁻¹ * principalTruncation (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ
    (quadraticSquareProfile W) X Z

def lowPrincipalMiddle (I J : Ideal O) (W : SchwartzMap ℝ ℂ) (X Y Z lengthScale : ℝ) : ℂ :=
  (6 : ℂ)⁻¹ * middleTruncation (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ
    (quadraticSquareProfile W) X Y Z lengthScale

def lowPrincipalError (I J : Ideal O) (W : SchwartzMap ℝ ℂ) (X Y Z lengthScale : ℝ) : ℂ :=
  (6 : ℂ)⁻¹ * truncationError (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ
    (quadraticSquareProfile W) X Y Z lengthScale

theorem lowPrincipalIdeal_truncated (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (X Y Z lengthScale : ℝ) (hX : 0 < X) :
    lowPrincipalIdeal I J W X =
      lowPrincipalMain I J W X Z + lowPrincipalMiddle I J W X Y Z lengthScale + lowPrincipalError I J W X Y Z lengthScale := by
  have he : lowPrincipalLattice I J W X =
      ∑' z : O, rowCoprimeMask (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ z *
        (if z = 0 then 0 else quadraticSquareProfile W (‖eisEmbedding z‖ ^ 2 / X)) := by
    apply tsum_congr
    intro z
    by_cases hz : z = 0
    · subst z
      simp only [jointMask_zero, zero_mul]
    · simp only [if_neg hz, quadraticSquareProfile_apply]
  rw [lowPrincipalIdeal_eq_lattice I J hI hJ W X hX, he]
  unfold lowPrincipalMain lowPrincipalMiddle lowPrincipalError truncationError
  ring

theorem gcdMaskPrimes_card_le (D : Ideal O) :
    (gcdMaskPrimes D).card ≤ 2 + (IdealMobiusDivisorSum.primeSupport D).card := by
  change (fixedBadPrimes ∪ IdealMobiusDivisorSum.primeSupport D).card ≤ _
  exact (Finset.card_union_le _ _).trans_eq (by rw [fixedBadPrimes_card])

theorem gcdMaskPrimes_subsets_bound (ε : ℝ) (hε : 0 < ε) (D : Ideal O) (hD : D ≠ 0) :
    (2 : ℝ) ^ (gcdMaskPrimes D).card ≤
      4 * supportConstant ε hε * (Ideal.absNorm D : ℝ) ^ ε := by
  calc
    _ ≤ (2 : ℝ) ^ (2 + (IdealMobiusDivisorSum.primeSupport D).card) :=
      pow_le_pow_right₀ (by norm_num) (gcdMaskPrimes_card_le D)
    _ = 4 * (2 : ℝ) ^ (IdealMobiusDivisorSum.primeSupport D).card := by rw [pow_add]; norm_num
    _ ≤ 4 * (supportConstant ε hε * (Ideal.absNorm D : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (support_card_bound ε hε D hD) (by norm_num)
    _ = _ := by ring

theorem lowPrincipalError_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (I J : Ideal O) (_hI : Admissible I) (_hJ : Admissible J)
        (W : SchwartzMap ℝ ℂ) (X Y Z lengthScale : ℝ),
        0 < X → 0 < Y → Y ≤ X → X ≤ Z → 0 ≤ lengthScale →
        ‖lowPrincipalError I J W X Y Z lengthScale‖ ≤
          (4 * supportConstant ε hε * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) ^ ε) *
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) *
          ((Y / X) ^ A + 1 / (1 + Z / X) ^ A +
            (X / Y) / ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A)) := by
  obtain ⟨s, C, hC, hb⟩ := truncationError_bound A
  refine ⟨s, C, hC, ?_⟩
  intro ε hε I J hI hJ W X Y Z lengthScale hX hY hYX hXZ hL
  have h := hb (fun P : gcdMaskPrimes (I * J) => P.val) Subtype.val_injective Finset.univ
    (quadraticSquareProfile W) X Y Z lengthScale hX hY hYX hXZ hL
  have hc := gcdMaskPrimes_subsets_bound ε hε (I * J) (mul_ne_zero hI.1 hJ.1)
  simp only [Finset.card_univ, Fintype.card_coe] at h
  simp only [map_mul, Nat.cast_mul] at hc
  have hnorm : ‖lowPrincipalError I J W X Y Z lengthScale‖ ≤
      ‖truncationError (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ
        (quadraticSquareProfile W) X Y Z lengthScale‖ := by
    unfold lowPrincipalError
    rw [norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    norm_num
  apply hnorm.trans (h.trans ?_)
  have hZ : 0 < Z := hX.trans_le hXZ
  gcongr

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss

theorem tsum_admissible_norm_cutoff (K : ℝ) (f : Ideal O → ℂ) :
    (∑' B : {B : Ideal O // Admissible B}, if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0) =
      ∑ B : idealRange K, f B.val := by
  let e : idealRange K → {B : Ideal O // Admissible B} :=
    fun B => ⟨B.val, (mem_idealRange.mp B.property).1⟩
  have he : Function.Injective e := by
    intro B C h
    apply Subtype.ext
    exact congrArg (fun D : {B : Ideal O // Admissible B} => D.val) h
  let F : {B : Ideal O // Admissible B} → ℂ := fun B =>
    if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0
  have hs : Function.support F ⊆ Set.range e := by
    intro B hB
    have hN : (Ideal.absNorm B.val : ℝ) ≤ K := by
      by_contra hn
      exact hB (if_neg hn)
    exact ⟨⟨B.val, mem_idealRange.mpr ⟨B.property, hN⟩⟩, Subtype.ext rfl⟩
  have ht := he.tsum_eq hs
  change (∑' B, F B) = _
  rw [← ht, tsum_fintype]
  apply Finset.sum_congr rfl
  intro B _
  exact if_pos (mem_idealRange.mp B.property).2

theorem originalPairLow_principal_finite
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (M K : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale) =
      ∑ B : idealRange K,
        (quadraticRow I (primaryGenerator B.val) * quadraticRow J (primaryGenerator B.val)) *
          ((6 : ℂ)⁻¹ * lowPrincipalLattice I J W (Real.sqrt (M / (Ideal.absNorm B.val : ℝ)))) := by
  rw [originalPairLow_principal_lattice I J hI hJ W M K hM]
  exact tsum_admissible_norm_cutoff K (fun B : Ideal O =>
    (quadraticRow I (primaryGenerator B) * quadraticRow J (primaryGenerator B)) *
      ((6 : ℂ)⁻¹ * lowPrincipalLattice I J W (Real.sqrt (M / (Ideal.absNorm B : ℝ)))))

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstCauchyArithmetic (activeGaussRowFactor)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem activeGaussRowFactor_norm_le_one
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S T : Finset ι) (e k : O) :
    ‖activeGaussRowFactor p hp hinj hg S T e k‖ ≤ 1 := by
  have hr (a : O) : ‖finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) S T)
      (fun i => hg i.val) (activeExponent S T) a‖ ≤ 1 := by
    rw [finiteSexticRow_activeSupport, norm_mul, norm_star]
    exact (mul_le_mul (finiteSquarefreeRow_norm_le_one _ hg _ _)
      (finiteSquarefreeRow_norm_le_one _ hg _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hGauss := FiniteGaussPhase.norm_canonicalProductGauss
    (fun i : activeSupport S T => p i.val) (fun i => hp i.val)
    (activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T)
    (fun i => hg i.val) (fun i => hc i.val) (activeExponent S T)
    (activeExponent_ne_zero S T) (activeExponent_lt_six S T)
  simp only [activeGaussRowFactor, norm_mul, norm_star, hGauss, one_mul]
  exact (mul_le_mul (hr e) (hr k) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem secondPairRadialMode_tail
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ (S T : Finset ι) (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ),
      0 < Y → 0 ≤ H →
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      (∑' k : {k : O // H ≤ scale * ‖eisEmbedding k‖^2},
        ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖) ≤
      (Y / ‖eisEmbedding n‖) *
        ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 scale)^2 * (1+H)^A)) := by
  obtain ⟨s,C,hC,hbound⟩ := EisensteinSchwartzPoisson.paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro S T e he W Y H hY hH
  dsimp only
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hp i.val)
  have hnorm : 0 < ‖eisEmbedding n‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero hn)
  have hscale : 0 < scale := div_pos hY
    (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he))) (sq_pos_of_pos hnorm))
  let tailSet : Set O := {k | H ≤ scale * ‖eisEmbedding k‖^2}
  let c := Y / ‖eisEmbedding n‖
  have hc0 : 0 ≤ c := (div_pos hY hnorm).le
  have hpnt (k : tailSet) : ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
      c * ‖EisensteinSchwartzPoisson.paperRadialFourier W (scale * ‖eisEmbedding k.val‖^2)‖ := by
    have ha : Y * ‖eisEmbedding k.val‖^2 / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2) =
        scale * ‖eisEmbedding k.val‖^2 := by dsimp [scale]; ring
    simp only [secondPairRadialMode, norm_mul]
    change ‖(Y : ℂ) / (‖eisEmbedding n‖ : ℂ)‖ * _ * _ ≤ _
    rw [ha, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hY, abs_of_pos hnorm]
    exact mul_le_of_le_one_right (by positivity)
      (activeGaussRowFactor_norm_le_one p hp hg hinj hc T S e k.val)
  have hmajor : Summable (fun k : tailSet =>
      c * ‖EisensteinSchwartzPoisson.paperRadialFourier W (scale * ‖eisEmbedding k.val‖^2)‖) :=
    ((EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hscale).subtype tailSet).mul_left c
  have hsmall : Summable (fun k : tailSet => ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpnt hmajor
  calc
    _ ≤ ∑' k : tailSet, c * ‖EisensteinSchwartzPoisson.paperRadialFourier W
          (scale * ‖eisEmbedding k.val‖^2)‖ := hsmall.tsum_le_tsum hpnt hmajor
    _ = c * ∑' k : tailSet, ‖EisensteinSchwartzPoisson.paperRadialFourier W
          (scale * ‖eisEmbedding k.val‖^2)‖ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (hbound W scale H hscale hH) hc0

end
section

open ActualEisensteinCubic

def secondExpansionPool {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) : Finset (SecondExpansionData ι) :=
  F.powerset.biUnion (fun G => G.powerset.biUnion (fun E =>
    F.powerset.biUnion (fun V => (K G E).image (fun k => ⟨G,E,V,k⟩))))

theorem mem_secondExpansionPool {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (x : SecondExpansionData ι) :
    x ∈ secondExpansionPool F K ↔
      x.sourceCommon ⊆ F ∧ x.divisor ⊆ x.sourceCommon ∧ x.overlap ⊆ F ∧
        x.frequency ∈ K x.sourceCommon x.divisor := by
  simp only [secondExpansionPool, Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨G,hG,E,hE,V,hV,k,hk,hx⟩
    subst x
    exact ⟨hG,hE,hV,hk⟩
  · rintro ⟨hG,hE,hV,hk⟩
    exact ⟨x.sourceCommon,hG,x.divisor,hE,x.overlap,hV,x.frequency,hk,rfl⟩

theorem sum_secondExpansionPool {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (H : SecondExpansionData ι → ℂ) :
    (∑ x ∈ secondExpansionPool F K, H x) =
      ∑ G ∈ F.powerset, ∑ E ∈ G.powerset, ∑ V ∈ F.powerset, ∑ k ∈ K G E, H ⟨G,E,V,k⟩ := by
  unfold secondExpansionPool
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro G hG
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro E hE
      rw [Finset.sum_biUnion]
      · apply Finset.sum_congr rfl
        intro V hV
        rw [Finset.sum_image]
        intro k hk k' hk' heq
        exact congrArg SecondExpansionData.frequency heq
      · intro V hV V' hV' hne
        apply Finset.disjoint_left.mpr
        intro x hx hx'
        obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨k',hk',heq⟩ := Finset.mem_image.mp hx'
        exact hne (congrArg SecondExpansionData.overlap heq).symm
    · intro E hE E' hE' hne
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      obtain ⟨V,hV,hx⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨V',hV',hx'⟩ := Finset.mem_biUnion.mp hx'
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨k',hk',heq⟩ := Finset.mem_image.mp hx'
      exact hne (congrArg SecondExpansionData.divisor heq).symm
  · intro G hG G' hG' hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨E,hE,V,hV,hx⟩ := (by simpa only [Finset.mem_biUnion] using hx)
    obtain ⟨E',hE',V',hV',hx'⟩ := (by simpa only [Finset.mem_biUnion] using hx')
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k',hk',heq⟩ := Finset.mem_image.mp hx'
    exact hne (congrArg SecondExpansionData.sourceCommon heq).symm

def secondExpansionSector {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) : Finset (SecondExpansionData ι) :=
  (secondExpansionPool F K).filter (fun x => x.sourceCommon \ x.divisor = R)

theorem sum_secondExpansionSector {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (H : SecondExpansionData ι → ℂ) :
    (∑ R ∈ F.powerset, ∑ x ∈ secondExpansionSector F K R, H x) =
      ∑ x ∈ secondExpansionPool F K, H x := by
  simp only [secondExpansionSector, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hR : x.sourceCommon \ x.divisor ∈ F.powerset :=
    Finset.mem_powerset.mpr ((Finset.sdiff_subset).trans ((mem_secondExpansionPool F K x).mp hx).1)
  rw [Finset.sum_eq_single_of_mem (x.sourceCommon \ x.divisor) hR]
  · simp
  · intro R hR hne
    simp [Ne.symm hne]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem secondExpansionSector_valid (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι)
    (x : SecondExpansionData ι) (hx : x ∈ secondExpansionSector F K R) :
    InSecondQuotientSector p (primeSubsetGenerator (fun i => Ideal.span {p i}) R) x := by
  obtain ⟨hx,hR⟩ := Finset.mem_filter.mp hx
  have hE := ((mem_secondExpansionPool F K x).mp hx).2.1
  refine ⟨hE,?_⟩
  rw [secondMaskQuotient_span, hR, primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator]

theorem truncatedSecondSource_eq_expansionPool
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      ∑ z : SecondRayIndex, secondExpansionSource p hp hcop hg F Ψ m c d z
        (secondExpansionPool F K) H H W Y := by
  rw [truncatedSecondSource_eq_child_sectors p hp hg hinj hcop hc hpr]
  simp only [secondExpansionSource, sum_secondExpansionPool]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.sum_coe_sort (s := G.powerset)]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro V hV
  apply Finset.sum_congr rfl
  intro k hk
  have hs : (⟨G,E.val,V,k⟩ : SecondExpansionData ι).divisor ⊆
      (⟨G,E.val,V,k⟩ : SecondExpansionData ι).sourceCommon := Finset.mem_powerset.mp E.property
  simp only [secondExpansionQuotient_of_subset p _ hs]
  simp only [mul_assoc]

theorem truncatedSecondSource_eq_fixed_sectors
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      ∑ z : SecondRayIndex, ∑ R ∈ F.powerset,
        secondExpansionSource p hp hcop hg F Ψ m c d z
          (secondExpansionSector F K R) H H W Y := by
  rw [truncatedSecondSource_eq_expansionPool p hp hcop hg hinj hc hpr]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [secondExpansionSource, sum_secondExpansionSector]

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn jLabel)
open JointLogSeparation (halfNormalizationCLM)

theorem normalized_truncatedSecondSource_eq_raw_sectors {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (Ψ : O →* ℂ) (m : O) (X Y : ℝ) (hX : 0 < X)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ, ℂ)) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (K : Finset ι → Finset ι → Finset O) :
    let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C *
      jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
    truncatedSecondSource p hp hg hinj F Ψ m c d
      (fun A => normalizedColumn p (fun S => g (columnLog p X S)) A) W Y K =
      ∑ z : SecondRayIndex, ∑ R ∈ F.powerset,
        actualSecondRawVariableSector p hp hcop hg B v₁ v₂ ε₁ ε₂
          ((secondExpansionSector F K R).image (expansionSupportData C D))
          (secondExpansionPushWeight C D (secondExpansionSector F K R)
            (secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y))
          F (secondRayMinus Ψ z) (secondRayPlus Ψ z) m
          (primeSubsetGenerator (fun i => Ideal.span {p i}) R)
          (halfNormalizationCLM U g) (halfNormalizationCLM U g) W
          (secondExpansionScale p X (primeSubsetGenerator (fun i => Ideal.span {p i}) R)) Y := by
  dsimp only
  rw [truncatedSecondSource_eq_fixed_sectors p hp hcop hg hinj hc hpr]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro R hR
  exact secondExpansionSource_eq_raw_variable_sector p hp hcop hg hinj hpr B C D F
    v₁ v₂ ε₁ ε₂ Ψ m _ z (secondExpansionSector F K R)
    (fun x hx => secondExpansionSector_valid p F K R x hx)
    X Y hX U hUc hUs g g W hU hU

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)

include hc

theorem secondPairRadialMode_summable_norm (S T : Finset ι) (e : O) (he : e ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun k : O => ‖secondPairRadialMode p hp hg hinj S T e k W Y‖) := by
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hp i.val)
  have hs : 0 < scale := div_pos hY
    (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he)))
      (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hn))))
  have hmajor := (EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hs).mul_left
    ‖(Y : ℂ)/(‖eisEmbedding n‖ : ℂ)‖
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hmajor
  intro k
  have ha : Y * ‖eisEmbedding k‖^2 / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2) =
      scale * ‖eisEmbedding k‖^2 := by dsimp [scale]; ring
  simp only [secondPairRadialMode, norm_mul]
  change ‖(Y : ℂ)/(‖eisEmbedding n‖ : ℂ)‖ * _ * _ ≤ _
  rw [ha]
  exact mul_le_of_le_one_right (by positivity)
    (activeGaussRowFactor_norm_le_one p hp hg hinj hc T S e k)

theorem secondPairRadialMode_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ (S T : Finset ι) (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ),
      0 < Y → 0 ≤ H → ∀ K : Finset O,
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      (∀ k : O, k ∉ K → H ≤ scale * ‖eisEmbedding k‖^2) →
      ‖∑' k : {k : O // k ∉ K}, secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
        (Y/‖eisEmbedding n‖) *
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 scale)^2*(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := secondPairRadialMode_tail p hp hg hinj hc A
  refine ⟨s,C,hC,?_⟩
  intro S T e he W Y H hY hH K
  dsimp only
  intro hK
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  let small : Set O := {k | k ∉ K}
  let large : Set O := {k | H ≤ scale * ‖eisEmbedding k‖^2}
  let f : small → large := fun k => ⟨k.val,hK k.val k.property⟩
  have hi : Function.Injective f := by
    intro a b heq
    exact Subtype.ext (congrArg (fun z : large => z.val) heq)
  have hs := secondPairRadialMode_summable_norm p hp hg hinj hc S T e he W Y hY
  calc
    _ ≤ ∑' k : small, ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ :=
      norm_tsum_le_tsum_norm (hs.subtype small)
    _ ≤ ∑' k : large, ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ :=
      (hs.subtype small).tsum_le_tsum_of_inj f hi (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
        (hs.subtype large)
    _ ≤ _ := hb S T e he W Y H hY hH

end SecondPassArithmetic

end

end OAI

end



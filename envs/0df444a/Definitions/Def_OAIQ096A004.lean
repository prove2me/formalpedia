-- Prove2me | Definitions.Def_OAIQ096A004
-- name    : OAIQ096A004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:32:04.077271+00:00
-- url     : https://prove2.me/theorems/29c3be67-a0d7-4022-8156-bb4c235fb61c
-- title:
--   Definitions bundle OAIQ096A004 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 236 declarations of OpenAI's Lean: 75 definitions, 9 inductive types or structures, 2 instances and 150 theorems. The definitions and types are `OAI.CubicFirstMoment.AngularKummerPrimeExplicitEstimate`, `OAI.CubicFirstMoment.AngularUnitCompatible`, `OAI.CubicFirstMoment.CompletedHeckeFiniteOrder`, `OAI.CubicFirstMoment.ComplexIdealSeries`, `OAI.CubicFirstMoment.ConductorMomentInstance`, `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity`, `OAI.CubicFirstMoment.CubicThetaArithmeticCover`, `OAI.CubicFirstMoment.CubicThetaBottomRow`, `OAI.CubicFirstMoment.CubicThetaBottomRow.completion`, `OAI.CubicFirstMoment.CubicThetaBottomRow.height`, `OAI.CubicFirstMoment.CubicThetaBottomRow.phase`, `OAI.CubicFirstMoment.CubicThetaBottomRow.rightMul`, `OAI.CubicFirstMoment.CubicThetaBottomRow.rightMulEquiv`, `OAI.CubicFirstMoment.CubicThetaBottomRow.shift`, `OAI.CubicFirstMoment.CubicThetaCoordinates`, `OAI.CubicFirstMoment.CubicThetaInvertedRow`, `OAI.CubicFirstMoment.CubicThetaPrimaryPair`, `OAI.CubicFirstMoment.CubicThetaPrimitiveRow`, `OAI.CubicFirstMoment.HuxleyLift`, `OAI.CubicFirstMoment.MetaplecticDualArgument`, `OAI.CubicFirstMoment.ShortArithmeticFactor`, `OAI.CubicFirstMoment.ShortFactorFamily`, `OAI.CubicFirstMoment.ShortFactorFamily.comp`, `OAI.CubicFirstMoment.ShortFactorFamily.cubicValue`, `OAI.CubicFirstMoment.ShortFactorFamily.mixedValue`, `OAI.CubicFirstMoment.ShortMomentInstance`, `OAI.CubicFirstMoment.angularCorrectionChar`, `OAI.CubicFirstMoment.angularKummerAnalyticConductor`, `OAI.CubicFirstMoment.angularKummerCharacter`, `OAI.CubicFirstMoment.angularUnitCorrection`, `OAI.CubicFirstMoment.complexOfRealCoords`, `OAI.CubicFirstMoment.cubicThetaBottomRow`, `OAI.CubicFirstMoment.cubicThetaFullComplex`, `OAI.CubicFirstMoment.cubicThetaKubotaCharacter`, `OAI.CubicFirstMoment.cubicThetaKubotaValue`, `OAI.CubicFirstMoment.cubicThetaPrimeConjugate`, `OAI.CubicFirstMoment.cubicThetaPrimeConjugatedMatrix`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootConjugate`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootElement`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootIwahori` and 44 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicGram_CubeExtraction`, `CubicGram_LatticeCounts`, `CubicGram_LatticePoisson`, `CubicGram_MixedPoisson`, `CubicGram_PeriodicPoisson`, `CubicGram_PrimaryNormalization`, `CubicGram_Reciprocity`, `CubicGram_ReciprocityKernel`, `CubicGram_SquarefreeGauss`, `CubicMoment_Angular_AngularAlgebra`, `CubicMoment_Angular_AngularHeckeCharacter`, `CubicMoment_Estimates_ConductorNeighborhoods`, `CubicMoment_Estimates_CubicNumeratorCharacter`, `CubicMoment_Estimates_CubicSupplementaryPeriodicityProof`, `CubicMoment_Estimates_FixedAngularHecke`, `CubicMoment_Estimates_HeckeCompletedOrder`, `CubicMoment_Estimates_HuxleyLiftedPacking`, `CubicMoment_Estimates_IdealDualDyads`, `CubicMoment_Estimates_IdealEulerExclusion`, `CubicMoment_Estimates_MixedCharacterSieve`, `CubicMoment_Estimates_MixedResidueCharacters`, `CubicMoment_Estimates_PrimaryHeckeCharacter`, `CubicMoment_Estimates_PrimeLogReplacement`, `CubicMoment_Estimates_PrimitiveResidueConductorKernel`, `CubicMoment_Estimates_PrimitiveResidueFourier`, `CubicMoment_Estimates_PublishedAngularKummerPrime`, `CubicMoment_Estimates_PublishedHecke`, `CubicMoment_Estimates_RamifiedPrimaryDecomposition`, `CubicMoment_Estimates_ResidueProducts`, `CubicMoment_Estimates_SchwartzLattice`, `CubicMoment_Estimates_ShortFactorLargeValues`, `CubicMoment_Estimates_ShortFactorMoments`, `CubicMoment_Estimates_ShortFactorSequences`, `CubicMoment_Estimates_ShortFactorUniform`, `CubicMoment_Estimates_ShortMoebius`, `CubicMoment_Estimates_ShortMoebiusFinite`, `CubicMoment_Estimates_ShortMoebiusPolynomials`, `CubicMoment_Theta_CubicThetaAnnularSeries`, `CubicMoment_Theta_CubicThetaArithmetic`, `CubicMoment_Theta_CubicThetaBottomRow`, `CubicMoment_Theta_CubicThetaBottomRowAction`, `CubicMoment_Theta_CubicThetaCoprimeShear`, `CubicMoment_Theta_CubicThetaCuspSeparation`, `CubicMoment_Theta_CubicThetaEisenstein`, `CubicMoment_Theta_CubicThetaEisensteinBounds`, `CubicMoment_Theta_CubicThetaEisensteinCusp`, `CubicMoment_Theta_CubicThetaEisensteinResidues`, `CubicMoment_Theta_CubicThetaFiniteCover`, `CubicMoment_Theta_CubicThetaFreeAction`, `CubicMoment_Theta_CubicThetaFullRows`, `CubicMoment_Theta_CubicThetaIncomingRows`, `CubicMoment_Theta_CubicThetaIncomingSmooth`, `CubicMoment_Theta_CubicThetaInvertedRows`, `CubicMoment_Theta_CubicThetaKubotaAlternative`, `CubicMoment_Theta_CubicThetaKubotaCharacter`, `CubicMoment_Theta_CubicThetaKubotaMultiplication`, `CubicMoment_Theta_CubicThetaKubotaProduct`, `CubicMoment_Theta_CubicThetaKubotaSupplement`, `CubicMoment_Theta_CubicThetaKubotaValue`, `CubicMoment_Theta_CubicThetaPrimaryIndex`, `CubicMoment_Theta_CubicThetaPrimeConjugation`, `CubicMoment_Theta_CubicThetaPrimeCubeConjugation`, `CubicMoment_Theta_CubicThetaPrimeCubeRootAction`, `CubicMoment_Theta_CubicThetaPrimeCubeRootAutomorphism`, `CubicMoment_Theta_CubicThetaPrimeCubeRootConjugation`, `CubicMoment_Theta_CubicThetaPrimeCubeRootMatrix`, `CubicMoment_Theta_CubicThetaPrimeCubeRootTranslation`, `CubicMoment_Theta_CubicThetaPrimeDilation`, `CubicMoment_Theta_CubicThetaPrimeIwahori`, `CubicMoment_Theta_CubicThetaPrimeRootAction`, `CubicMoment_Theta_CubicThetaPrimeRootCharacter`, `CubicMoment_Theta_CubicThetaPrimeRootConjugation`, `CubicMoment_Theta_CubicThetaPrimeRootMatrix`, `CubicMoment_Theta_CubicThetaPrimeRootOperators`, `CubicMoment_Theta_CubicThetaPrimeRootSubgroup`, `CubicMoment_Theta_CubicThetaPrimeRootTranslation`, `CubicMoment_Theta_CubicThetaProperAction`, `CubicMoment_Theta_CubicThetaRowGaussBounds`, `CubicMoment_Transform_MetaplecticCompletion`, `CubicMoment_Transform_MetaplecticVoronoi`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A000` and `OAIQ096A001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A007`, `OAIQ096A008`, `OAIQ096A009` and `OAIQ096A010`; the statements `OAI_CubicFirstMoment_ProfileControl_low_coprime_height_real`, `OAI_CubicFirstMoment_ProfileControl_smallB_nonzero_variance_height_power`, `OAI_CubicFirstMoment_angular_corrected_dispersion_asymptotic_actual`, `OAI_CubicFirstMoment_angular_distinguishedStoppedDyad_early_bound_actual`, `OAI_CubicFirstMoment_angular_full_prime_product_height_bilinear`, `OAI_CubicFirstMoment_angular_largePrimeTupleOrdinaryHighSum_isLittleO_actual`, `OAI_CubicFirstMoment_angular_largePrimeTuplePiece_nonflat_high_bound_actual`, `OAI_CubicFirstMoment_angular_scaleFirstMiddleSum_isLittleO_actual`, `OAI_CubicFirstMoment_angular_stopped_product_transfer`, `OAI_CubicFirstMoment_kummer_unweighted_from_primitive`, `OAI_CubicFirstMoment_largePrimeTuplePiece_nonflat_high_bound_actual`, `OAI_CubicFirstMoment_primeGroupTail_common_row_height_power`, `OAI_CubicFirstMoment_primeGroupTail_wide_bilinear_log_saving`, `OAI_CubicFirstMoment_rough_prime_corrected_bilinear_actual`, `OAI_CubicFirstMoment_stopped_corrected_dispersion_log_saving_actual`, `OAI_CubicFirstMoment_stopped_product_bilinear_log_saving_actual` and `OAI_CubicFirstMoment_stopped_product_transfer`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A000
import Definitions.Def_OAIQ096A001

section
-- module Solutions.OAIQ096_CM.CubicGram_PrimaryNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique primary associates and canonical prime factorization. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid

lemma primaryNormalize_eq_self {z : Eisenstein} (hz : primary z) : primaryNormalize z = z := by
  exact primary_associated_eq
    (primaryNormalize_primary (unit_residue_of_dvd_primary hz (dvd_refl z))) hz
    (primaryNormalize_associated z).symm

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_ReciprocityKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-field Frobenius relations and distinct-character reciprocity. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable

noncomputable section
open scoped BigOperators
open AddChar MulChar

namespace CubicFirstMoment

lemma cubic_reciprocity_frobenius {p r : Eisenstein} (hp : primaryPrime p)
    (hr : primaryPrime r) (hdiff : ringChar (Residues r) ≠ ringChar (Residues p)) :
    cubicSymbolAtPrime r p ^ 2 * cubicSymbolAtPrime r (conjugate p) *
      cubicSymbolAtPrime p r * cubicSymbolAtPrime p (conjugate r) = 1 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : (modulus r).IsPrime := (Ideal.span_singleton_prime hr.2.ne_zero).mpr hr.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Finite (Residues r) := finite_residues hr.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Fintype (Residues r) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  let : Field (Residues r) := Fintype.fieldOfDomain _
  let χ := (cubicResidueCharE p hp).ringHomComp (Ideal.Quotient.mk (modulus r))
  have hχ : χ^3 = 1 := by
    dsimp [χ]
    rw [MulChar.ringHomComp_pow, cubicResidueCharE_cube hp, MulChar.ringHomComp_one]
  have hminus : χ (-1) = 1 := by
    change Ideal.Quotient.mk (modulus r) (cubicResidueCharE p hp (-1)) = 1
    rw [cubicResidueCharE_neg_one hp, map_one]
  have hcardp : Fintype.card (Residues p) = normNat p := by
    rw [← Nat.card_eq_fintype_card, residues_card hp.2.ne_zero]
  have hcardr : Fintype.card (Residues r) = normNat r := by
    rw [← Nat.card_eq_fintype_card, residues_card hr.2.ne_zero]
  have hthree : 3 ∣ Fintype.card (Residues r) - 1 := by
    rw [hcardr]
    exact primaryPrime_norm_sub_one_dvd_three hr
  have hJ : jacobiSum χ χ = Ideal.Quotient.mk (modulus r) (-p) := by
    dsimp [χ]
    rw [jacobiSum_ringHomComp, ← primeJacobi_eq_sumE hp, primeJacobi_eq_neg hp]
  have hrel := ReciprocityKernel.cubic_jacobi_card_relation χ hχ
    (cubicResidueCharE_ringHomComp_ne_one hp hr) hminus hthree hdiff
  rw [hJ, hcardp, hcardr] at hrel
  let z := cubicResidueCharE r hr (Ideal.Quotient.mk (modulus r) ((normNat p : Eisenstein)*(-p)))
  let w := cubicResidueCharE p hp (Ideal.Quotient.mk (modulus p) (normNat r : Eisenstein))
  have hred : Ideal.Quotient.mk (modulus r) (z*w) = 1 := by
    rw [map_mul]
    change Ideal.Quotient.mk (modulus r) (cubicResidueCharE r hr _) *
      Ideal.Quotient.mk (modulus r) w = 1
    rw [cubicResidueCharE_euler hr, map_mul, map_natCast]
    exact hrel
  have hzw : z*w ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hred
    exact zero_ne_one hred
  have hz : z^3 = 1 := cubicResidueCharE_value_cube hr (mul_ne_zero_iff.mp hzw).1
  have hw : w^3 = 1 := cubicResidueCharE_value_cube hp (mul_ne_zero_iff.mp hzw).2
  have hmul : z*w = 1 := cubeRoot_reduce_inj hr (by rw [mul_pow, hz, hw, one_mul])
    (one_pow 3) (hred.trans (map_one _).symm)
  have hc := congrArg (fun v : Eisenstein => (v : ℂ)) hmul
  simp only [z, w, Subalgebra.coe_mul, Subalgebra.coe_one,
    cubicResidueCharE_coe, cubicResidueChar_mk] at hc
  rw [normNat_cast_eq_mul_conjugate, normNat_cast_eq_mul_conjugate,
    cubicSymbolAtPrime_mul hr, cubicSymbolAtPrime_mul hr,
    cubicSymbolAtPrime_neg hr, cubicSymbolAtPrime_mul hp] at hc
  calc
    _ = (cubicSymbolAtPrime r p * cubicSymbolAtPrime r (conjugate p) *
        cubicSymbolAtPrime r p) * (cubicSymbolAtPrime p r * cubicSymbolAtPrime p (conjugate r)) := by ring
    _ = 1 := hc

theorem cubic_reciprocity_distinct_char {p r : Eisenstein} (hp : primaryPrime p)
    (hr : primaryPrime r) (hdiff : ringChar (Residues r) ≠ ringChar (Residues p)) :
    cubicSymbolAtPrime r p = cubicSymbolAtPrime p r := by
  have hpr := cubic_reciprocity_frobenius hp hr hdiff
  have hrp := cubic_reciprocity_frobenius hr hp hdiff.symm
  calc
    cubicSymbolAtPrime r p = cubicSymbolAtPrime r p * 1 := (mul_one _).symm
    _ = cubicSymbolAtPrime r p * (cubicSymbolAtPrime p r ^ 2 *
        cubicSymbolAtPrime p (conjugate r) * cubicSymbolAtPrime r p *
          cubicSymbolAtPrime r (conjugate p)) := by rw [hrp]
    _ = cubicSymbolAtPrime p r * (cubicSymbolAtPrime r p ^ 2 *
        cubicSymbolAtPrime r (conjugate p) * cubicSymbolAtPrime p r *
          cubicSymbolAtPrime p (conjugate r)) := by ring
    _ = cubicSymbolAtPrime p r := by rw [hpr, mul_one]

end CubicFirstMoment
end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SquarefreeGauss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Composite residue characters, Chinese remainders and squarefree Gauss norms. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid

lemma norm_cubicSymbolAtPrime_of_isCoprime {p v : Eisenstein} (hp : primaryPrime p)
    (hv : IsCoprime p v) : ‖cubicSymbolAtPrime p v‖ = 1 := by
  have hv' := residue_isUnit_of_isCoprime hv
  obtain ⟨j,hj,_⟩ := cubicSymbol_euler_exists_unique hp hv'
  rw [cubicSymbol_euler_value hp hv' j hj, norm_pow,
    (omega_primitive.isOfFinOrder (by norm_num)).norm_eq_one, one_pow]

lemma norm_cubicSymbol_of_isCoprime {b v : Eisenstein} (hb : primary b)
    (hv : IsCoprime b v) : ‖cubicSymbol b v‖ = 1 := by
  unfold cubicSymbol
  rw [← normHom_apply, map_multiset_prod, Multiset.map_map]
  apply Multiset.prod_eq_one
  intro z hz
  obtain ⟨p,hp,rfl⟩ := Multiset.mem_map.mp hz
  have hd : primaryNormalize p ∣ b :=
    (primaryNormalize_associated p).dvd_iff_dvd_left.mp (dvd_of_mem_normalizedFactors hp)
  exact norm_cubicSymbolAtPrime_of_isCoprime
    ⟨primaryNormalize_primary (unit_residue_of_dvd_primary hb (dvd_of_mem_normalizedFactors hp)),
      prime_primaryNormalize (prime_of_normalized_factor p hp)⟩
    (hv.of_isCoprime_of_dvd_left hd)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Reciprocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full cubic reciprocity and twisted multiplicativity of Gauss sums. -/

section

noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_one : primary (1 : Eisenstein) := by simp [primary]

lemma cubic_reciprocity_conjugate {p : Eisenstein} (hp : primaryPrime p) :
    cubicSymbolAtPrime (conjugate p) p = cubicSymbolAtPrime p (conjugate p) := by
  by_cases heq : p = conjugate p
  · rw [← heq]
  let t : Eisenstein := -(p + conjugate p)
  have ht : primary t := by
    obtain ⟨a, ha⟩ := hp.1
    obtain ⟨b, hb⟩ := primary_conjugate hp.1
    refine ⟨-a-b-1, ?_⟩
    dsimp [t]
    linear_combination -ha-hb
  have htconj : conjugate t = t := by simp [t, add_comm]
  have hnot : ¬p ∣ t := by
    intro h
    have hsum : p ∣ p + conjugate p := by simpa only [t, dvd_neg] using h
    have hpc : p ∣ conjugate p := (dvd_add_right (dvd_refl p)).mp hsum
    exact heq (primary_associated_eq hp.1 (primary_conjugate hp.1)
      (hp.2.associated_of_dvd (primaryPrime_conjugate hp).2 hpc))
  have hnotconj : ¬conjugate p ∣ t := by
    intro h
    have hh := map_dvd conjugate h
    rw [conjugate_conjugate, htconj] at hh
    exact hnot hh
  have hrec : cubicSymbol t p = cubicSymbolAtPrime p t := by
    apply reciprocity_of_prime_divisor_relation hp ht
    intro q hq hqt
    apply cubic_reciprocity_distinct_char hp hq
    intro hc
    rcases same_char_primary_primes hp hq hc with rfl | rfl
    · exact hnot hqt
    · exact hnotconj hqt
  have hA : cubicSymbolAtPrime p t = cubicSymbolAtPrime p (conjugate p) := by
    calc
      _ = cubicSymbolAtPrime p (-conjugate p) := by
        apply cubicSymbolAtPrime_congr
        apply residue_eq_of_dvd_sub
        refine ⟨-1, ?_⟩
        dsimp [t]
        ring
      _ = _ := cubicSymbolAtPrime_neg hp _
  have hfixed : cubicSymbol t p = star (cubicSymbol t p) := by
    calc
      _ = cubicSymbol t (-conjugate p) := by
        apply cubicSymbol_congr
        apply residue_eq_of_dvd_sub
        refine ⟨-1, ?_⟩
        dsimp [t]
        ring
      _ = cubicSymbol t (conjugate p) := cubicSymbol_neg ht _
      _ = cubicSymbol (conjugate t) (conjugate p) := by rw [htconj]
      _ = _ := cubicSymbol_conjugate ht p
  rw [hrec, hA] at hfixed
  calc
    _ = star (cubicSymbolAtPrime p (conjugate p)) := by
      simpa only [conjugate_conjugate] using cubicSymbolAtPrime_conjugate hp (conjugate p)
    _ = _ := hfixed.symm

theorem cubic_reciprocity_prime {p r : Eisenstein} (hp : primaryPrime p)
    (hr : primaryPrime r) : cubicSymbolAtPrime r p = cubicSymbolAtPrime p r := by
  by_cases hc : ringChar (Residues r) = ringChar (Residues p)
  · rcases same_char_primary_primes hp hr hc with rfl | rfl
    · rfl
    · exact cubic_reciprocity_conjugate hp
  · exact cubic_reciprocity_distinct_char hp hr hc

theorem cubic_reciprocity {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    cubicSymbol a b = cubicSymbol b a := by
  revert b
  apply primary_induction (b := a) ?_ ?_ ha
  · intro b hb
    rw [cubicSymbol_one_lower]
    unfold cubicSymbol
    have h : ∀ p ∈ normalizedFactors b,
        cubicSymbolAtPrime (primaryNormalize p) 1 = 1 := by
      intro p hp
      apply cubicSymbolAtPrime_one
      exact ⟨primaryNormalize_primary (unit_residue_of_dvd_primary hb
        (dvd_of_mem_normalizedFactors hp)), prime_primaryNormalize (prime_of_normalized_factor p hp)⟩
    symm
    apply Multiset.prod_eq_one
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hz
    exact h p hp
  · intro p a hp ha ih b hb
    rw [cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero ha),
      cubicSymbol_prime hp, cubicSymbol_mul_upper hb, ih hb]
    congr 1
    symm
    exact reciprocity_of_prime_divisor_relation hp hb
      (fun q hq _ => cubic_reciprocity_prime hp hq)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticePoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eisenstein real coordinates, measure factors and translated lattice Poisson summation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology

namespace CubicFirstMoment

def complexOfRealCoords : (Fin 2 → ℝ) →ₗ[ℝ] ℂ where
  toFun x := (x 0 : ℂ) + (x 1 : ℂ) * omega
  map_add' x y := by simp only [Pi.add_apply, Complex.ofReal_add]; ring
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
      Complex.real_smul]
    ring

lemma complexOfRealCoords_injective : Function.Injective complexOfRealCoords := by
  intro x y h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  change ((x 0 : ℂ) + (x 1 : ℂ) * omega).im =
    ((y 0 : ℂ) + (y 1 : ℂ) * omega).im at him
  change ((x 0 : ℂ) + (x 1 : ℂ) * omega).re =
    ((y 0 : ℂ) + (y 1 : ℂ) * omega).re at hre
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    omega_im, omega_re, zero_mul, zero_add, add_zero] at him
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
    omega_im, omega_re, zero_mul, sub_zero] at hre
  have hs : 0 < Real.sqrt (3 : ℝ) := by positivity
  have he : x 1 = y 1 := (mul_right_cancel₀ (by positivity : Real.sqrt (3 : ℝ) / 2 ≠ 0)) him
  ext i
  fin_cases i
  · change x 0 = y 0
    linarith
  · exact he

lemma complexOfRealCoords_surjective : Function.Surjective complexOfRealCoords := by
  intro z
  refine ⟨![z.re + z.im / Real.sqrt 3, 2 * z.im / Real.sqrt 3], ?_⟩
  exact (complex_coordinates z).symm

def eisensteinRealCoords : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
  (LinearEquiv.ofBijective complexOfRealCoords
    ⟨complexOfRealCoords_injective, complexOfRealCoords_surjective⟩).toContinuousLinearEquiv

@[simp] lemma eisensteinRealCoords_apply (x : Fin 2 → ℝ) :
    eisensteinRealCoords x = (x 0 : ℂ) + (x 1 : ℂ) * omega := rfl

def traceLambda : ℂ := 1 + 2 * omega

lemma traceLambda_eq : traceLambda = (Real.sqrt 3 : ℂ) * Complex.I := by
  rw [traceLambda, omega_eq]
  push_cast
  ring

lemma traceLambda_ne_zero : traceLambda ≠ 0 := by
  rw [traceLambda_eq]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) Complex.I_ne_zero

lemma dualRealCoords_trace (x y : Fin 2 → ℝ) :
    tracePair (eisensteinRealCoords x) (dualRealCoords y) = ∑ i, x i * y i := by
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  simp only [tracePair, eisensteinRealCoords_apply, dualRealCoords,
    Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.sub_im, Complex.mul_im, omega_re, omega_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, zero_add, add_zero,
    zero_sub, sub_zero, mul_one, Fin.sum_univ_two]
  field_simp
  ring

lemma dualRealCoords_eq (y : Fin 2 → ℝ) :
    dualRealCoords y =
      ((y 0 + y 1 : ℝ) + (y 0 : ℂ) * omega) / traceLambda := by
  apply (eq_div_iff traceLambda_ne_zero).mpr
  rw [traceLambda_eq, omega_eq]
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  simp only [dualRealCoords]
  push_cast
  field_simp
  linear_combination -(y 0 + 2 * y 1 : ℂ) * (Complex.I_sq)

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_PeriodicPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic lattice Poisson summation and exact trace frequencies. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def lambdaE : Eisenstein := 1 + 2 * omegaE

lemma lambdaE_sq : lambdaE ^ 2 = -3 := by
  dsimp [lambdaE]
  linear_combination 4 * omegaE_quadratic

lemma primary_coprime_lambda {c : Eisenstein} (hc : primary c) :
    IsCoprime c lambdaE := by
  obtain ⟨k, hk⟩ := hc
  refine ⟨1, lambdaE * k, ?_⟩
  linear_combination hk + k * lambdaE_sq

lemma tracePair_div_lambda_integral (z : Eisenstein) :
    ∃ n : ℤ, tracePair (z : ℂ) (1 / traceLambda) = (n : ℝ) := by
  obtain ⟨⟨a,b⟩, rfl⟩ := ofCoords_surjective z
  refine ⟨b, ?_⟩
  have hd : dualRealCoords ![0, 1] = 1 / traceLambda := by
    rw [dualRealCoords_eq]
    simp
  have hc : (ofCoords a b : ℂ) = eisensteinRealCoords ![(a : ℝ), (b : ℝ)] := by
    simp [eisensteinRealCoords_apply, ofCoords_coe]
  rw [hc, ← hd, dualRealCoords_trace]
  simp [Fin.sum_univ_two]

lemma tracePhase_div_lambda_one (z : Eisenstein) :
    (Real.fourierChar (tracePair (z : ℂ) (1 / traceLambda)) : ℂ) = 1 := by
  obtain ⟨n, hn⟩ := tracePair_div_lambda_integral z
  rw [hn, fourierChar_int]

lemma tracePhase_congr {c v w : Eisenstein} (hc : c ≠ 0) (h : Eisenstein)
    (he : Ideal.Quotient.mk (modulus c) v = Ideal.Quotient.mk (modulus c) w) :
    (Real.fourierChar (tracePair (v : ℂ) ((h : ℂ) / ((c : ℂ) * traceLambda))) : ℂ) =
      (Real.fourierChar (tracePair (w : ℂ) ((h : ℂ) / ((c : ℂ) * traceLambda))) : ℂ) := by
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  have hc' : (c : ℂ) ≠ 0 := fun h => hc (Subtype.ext h)
  have hv : (v : ℂ) = (w : ℂ) + (c : ℂ) * (k : ℂ) := by
    exact_mod_cast (show v = w+c*k by linear_combination hk)
  rw [hv, tracePair_add_left, AddChar.map_add_eq_mul, Circle.coe_mul]
  have hp : tracePair ((c : ℂ) * (k : ℂ)) ((h : ℂ) / ((c : ℂ) * traceLambda)) =
      tracePair ((k*h : Eisenstein) : ℂ) (1 / traceLambda) := by
    unfold tracePair
    congr 2
    push_cast
    field_simp
  rw [hp, tracePhase_div_lambda_one, mul_one]

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_MixedPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primary mixed characters and squarefree coset Poisson summation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicSymbol_cube_of_isCoprime {c : Eisenstein} (hc : primary c)
    (v : Eisenstein) (hv : IsCoprime c v) : cubicSymbol c v ^ 3 = 1 := by
  revert v
  apply primary_induction (b := c) ?_ ?_ hc
  · intro v _
    rw [cubicSymbol_one_lower, one_pow]
  · intro p b hp hb ih v hv
    rw [cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero hb), mul_pow,
      cubicSymbol_prime hp, cubicSymbolAtPrime_unit_cube hp
        (residue_isUnit_of_isCoprime hv.of_mul_left_left), ih v hv.of_mul_left_right,
      one_mul]

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubeExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primary cube decomposition and finite operator block bounds. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicSymbol_pow_upper {p : Eisenstein} (hp : primary p) (a : Eisenstein) (k : ℕ) :
    cubicSymbol p (a^k) = cubicSymbol p a ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    apply primary_induction (b := p) ?_ ?_ hp
    · exact cubicSymbol_one_lower 1
    · intro q b hq hb ih
      rw [cubicSymbol_mul_lower hq.2.ne_zero (primary_ne_zero hb),
        cubicSymbol_prime hq, cubicSymbolAtPrime_one hq, ih, one_mul]
  | succ k ih => rw [pow_succ, cubicSymbol_mul_upper hp, ih, pow_succ]

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticeCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eisenstein lattice counts and arbitrarily small divisor losses. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma one_le_norm {a : Eisenstein} (ha : a ≠ 0) : 1 ≤ norm a := by
  rw [← normNat_cast]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => ha (norm_eq_zero_iff.mp
    (by rw [← normNat_cast, h]; simp)))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Algebra of fixed angular prime moments

The angular weight is the phase of a nonzero Eisenstein integer raised to
an integer power.  These elementary facts ensure that fixed angular
weights preserve absolute values and distribute through finite prime sums.
-/

noncomputable section

open scoped BigOperators

namespace CubicFirstMoment

@[simp] theorem theta_add (ℓ m : ℤ) {a : Eisenstein} (ha : a ≠ 0) :
    theta (ℓ + m) a = theta ℓ a * theta m a := by
  have ha' : (a : ℂ) ≠ 0 := fun h => ha (Subtype.ext h)
  exact zpow_add₀ (div_ne_zero ha' (by exact_mod_cast norm_ne_zero_iff.mpr ha')) _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The short Möbius identity on Eisenstein ideals

Nonzero Eisenstein ideals are represented by their finite prime-ideal
exponent vectors. Their arithmetic functions form the multivariate power
series ring: its multiplication is exactly finite Dirichlet convolution.
The norm below is the norm of the product of prime representatives, so
the support statements retain the actual multiplicative ideal norm.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def idealPrimeRepresentative (p : EisensteinIdealPrime) : Eisenstein := Quotient.out p.val

/-- A generator of the ideal represented by its prime exponent vector. -/
def idealExponentGenerator (ν : EisensteinIdealExponent) : Eisenstein :=
  ν.prod (fun p k => idealPrimeRepresentative p ^ k)

def idealExponentNorm (ν : EisensteinIdealExponent) : ℝ :=
  (normNat (idealExponentGenerator ν) : ℝ)

/-- The exponent vector of every nonzero Eisenstein principal ideal. -/
def idealExponentOf (a : Eisenstein) : EisensteinIdealExponent :=
  (Associates.factors' a).toFinsupp

def idealZeta : EisensteinArithmeticFunction := fun _ => 1

/-- The ideal Möbius function, characterized as the Dirichlet inverse of
the constant-one arithmetic function. -/
def idealMoebiusSeries : EisensteinArithmeticFunction := idealZeta⁻¹

def shortIdealMoebius (F : ℝ) : EisensteinArithmeticFunction :=
  fun ν => if idealExponentNorm ν ≤ Real.sqrt F then MvPowerSeries.coeff ν idealMoebiusSeries else 0

def idealLogNorm : EisensteinArithmeticFunction := fun ν => Real.log (idealExponentNorm ν)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedHecke
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite-order Hecke prime input

The finite-order Hecke prime-sum input specializes to independent prime
factors using the elementary character laws.

The input is the cubic-character consequence of Thorner--Zaman,
*A unified and improved Chebotarev density theorem*, Algebra & Number
Theory 13 (2019), Theorem 1.4, in the Siegel–Walfisz form for cubic Hecke characters.  Only finite-order characters occur in this input;
smooth weights and norm twists follow by partial summation.
-/

noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace CubicFirstMoment

theorem mixedCubic_one {q₁ q₂ : Eisenstein}
    (h₁ : primary q₁) (h₂ : primary q₂) : mixedCubic q₁ q₂ 1 = 1 := by
  rw [mixedCubic, cubic_reciprocity h₁ (by norm_num [primary]),
    cubic_reciprocity h₂ (by norm_num [primary]),
    cubicSymbol_one_lower, cubicSymbol_one_lower, star_one, mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short ideal convolution identity evaluated on actual primary
character polynomials. All sums below are finite divisor sums. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Canonical primary generator on the ideals prime to three. We use it
only for exponent vectors below an actual primary principal ideal. -/
def idealPrimaryGenerator (ν : EisensteinIdealExponent) : Eisenstein :=
  primaryNormalize (idealExponentGenerator ν)

/-- Real ideal coefficients evaluated against a character of primary
Eisenstein elements. -/
def idealCharacterCoeff (A : EisensteinArithmeticFunction) (χ : Eisenstein → ℂ)
    (ν : EisensteinIdealExponent) : ℂ :=
  ((MvPowerSeries.coeff ν A : ℝ) : ℂ)*χ (idealPrimaryGenerator ν)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite primary ideal polynomials and their actual Eisenstein-element
realizations. These sums omit the ramified prime above three. They are
not identified with the complete ideal series of `IdealMellinSeries`. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- The corresponding finite ideal set, explicitly restricted to ideals
with a primary generator, hence prime to the ramified prime. -/
def primaryIdealBall (Y : ℝ) : Finset EisensteinIdealExponent :=
  (primaryElementBall Y).image idealExponentOf

/-- The primary ideal character polynomial with an arbitrary arithmetic
coefficient function. -/
def primaryIdealPolynomial (Y : ℝ) (A : EisensteinArithmeticFunction)
    (χ : Eisenstein → ℂ) : ℂ :=
  ∑ ν ∈ primaryIdealBall Y, idealCharacterCoeff A χ ν

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerExclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Euler exclusions on the complete ideal lattice. The full norm
ball includes the ramified prime; excluding it is an explicit choice of
prime set, and every rescaling factor is retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[simp] lemma primeSetExponent_apply (S : Finset EisensteinIdealPrime)
    (p : EisensteinIdealPrime) : primeSetExponent S p = if p ∈ S then 1 else 0 := by
  simp [primeSetExponent,Finsupp.single_apply]

@[simp] lemma idealExponentNorm_zero : idealExponentNorm 0 = 1 := by
  simp [idealExponentNorm,idealExponentGenerator,normNat,norm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MixedResidueCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mixed cubic residue characters and their finite Fourier transform. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- This character is defined at composite conductors, rather than supplied as
an abstract character agreeing with the desired cubic symbol. -/
def mixedResidueChar (a b : Eisenstein) (ha : primary a) (hb : primary b) :
    MulChar (Residues (a*b)) ℂ where
  toFun x := mixedCubic a b (residueRepresentative (a*b) x)
  map_one' := by
    rw [mixedCubic_congr (show
      Ideal.Quotient.mk (modulus (a*b)) (residueRepresentative (a*b) 1) =
      Ideal.Quotient.mk (modulus (a*b)) 1 by rw [residueRepresentative_spec,map_one])]
    exact mixedCubic_one ha hb
  map_mul' x y := by
    rw [mixedCubic_congr (show
      Ideal.Quotient.mk (modulus (a*b)) (residueRepresentative (a*b) (x*y)) =
      Ideal.Quotient.mk (modulus (a*b))
        (residueRepresentative (a*b) x*residueRepresentative (a*b) y) by
          rw [map_mul,residueRepresentative_spec,residueRepresentative_spec,
            residueRepresentative_spec])]
    exact mixedCubic_mul ha hb _ _
  map_nonunit' x hx := mixedCubic_eq_zero_of_nonunit ha hb _ (by
    rwa [residueRepresentative_spec])

@[simp] lemma mixedResidueChar_mk {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (v : Eisenstein) :
    mixedResidueChar a b ha hb (Ideal.Quotient.mk (modulus (a*b)) v) =
      mixedCubic a b v := mixedCubic_congr (residueRepresentative_spec _ _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MixedCharacterSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conductor-by-conductor Gauss transfer for actual squarefree mixed characters. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_coprime_three {a : Eisenstein} (ha : primary a) : IsCoprime a 3 := by
  obtain ⟨k,hk⟩ := ha
  refine ⟨1,-k,?_⟩
  linear_combination hk

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryHeckeCharacter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite character attached to the primary mixed cubic
symbol. Including the modulus 3 makes primary normalization periodic
and removes its dependence on the choice of a unit associate. -/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma isCoprime_of_residue_isUnit {q x : Eisenstein}
    (hx : IsUnit (Ideal.Quotient.mk (modulus q) x)) : IsCoprime q x := by
  obtain ⟨u,hu⟩ := hx
  obtain ⟨v,hv⟩ := Ideal.Quotient.mk_surjective (u⁻¹ : (Residues q)ˣ).val
  have he : Ideal.Quotient.mk (modulus q) (x*v) = Ideal.Quotient.mk (modulus q) 1 := by
    rw [map_mul,← hu,hv,map_one]
    exact u.mul_inv
  obtain ⟨w,hw⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  refine ⟨-w,v,?_⟩
  linear_combination hw

lemma primaryNormalize_mul_of_residue_units {x y : Eisenstein}
    (hx : IsUnit (Ideal.Quotient.mk (modulus 3) x))
    (hy : IsUnit (Ideal.Quotient.mk (modulus 3) y)) :
    primaryNormalize (x*y) = primaryNormalize x*primaryNormalize y := by
  apply primary_associated_eq
    (primaryNormalize_primary (by rw [map_mul]; exact hx.mul hy))
    (primary_mul (primaryNormalize_primary hx) (primaryNormalize_primary hy))
  exact (primaryNormalize_associated (x*y)).symm.trans
    ((primaryNormalize_associated x).mul_mul (primaryNormalize_associated y))

def primaryMixedLift (a b x : Eisenstein) : ℂ :=
  if IsUnit (Ideal.Quotient.mk (modulus 3) x) then
    mixedCubic a b (primaryNormalize x) else 0

lemma primaryMixedLift_primary {a b x : Eisenstein} (hx : primary x) :
    primaryMixedLift a b x = mixedCubic a b x := by
  rw [primaryMixedLift,ite_eq_left (unit_residue_of_dvd_primary hx (dvd_refl x)),
    primaryNormalize_eq_self hx]

lemma primaryMixedLift_one {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    primaryMixedLift a b 1 = 1 := by
  rw [primaryMixedLift_primary (by norm_num [primary]),mixedCubic_one ha hb]

lemma primaryMixedLift_mul {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (x y : Eisenstein) :
    primaryMixedLift a b (x*y) = primaryMixedLift a b x*primaryMixedLift a b y := by
  by_cases hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · by_cases hy : IsUnit (Ideal.Quotient.mk (modulus 3) y)
    · simp only [primaryMixedLift,map_mul,IsUnit.mul_iff,hx,hy,true_and,ite_true, if_true]
      rw [primaryNormalize_mul_of_residue_units hx hy,mixedCubic_mul ha hb]
    · simp [primaryMixedLift,map_mul,IsUnit.mul_iff,hx,hy]
  · simp [primaryMixedLift,map_mul,IsUnit.mul_iff,hx]

lemma primaryMixedLift_congr_parts {a b x y : Eisenstein}
    (h3 : Ideal.Quotient.mk (modulus 3) x = Ideal.Quotient.mk (modulus 3) y)
    (hq : Ideal.Quotient.mk (modulus (a*b)) x = Ideal.Quotient.mk (modulus (a*b)) y) :
    primaryMixedLift a b x = primaryMixedLift a b y := by
  by_cases hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · have hy : IsUnit (Ideal.Quotient.mk (modulus 3) y) := h3 ▸ hx
    obtain ⟨u,hu⟩ := primaryNormalize_associated x
    have hprim : primary (y*(u:Eisenstein)) := by
      apply (primary_iff_residue_one _).mpr
      rw [map_mul,← h3,← map_mul,hu]
      exact (primary_iff_residue_one _).mp (primaryNormalize_primary hx)
    have hnorm : primaryNormalize y = y*(u:Eisenstein) :=
      primary_associated_eq (primaryNormalize_primary hy) hprim (by
        exact (primaryNormalize_associated y).symm.trans ⟨u,rfl⟩)
    simp only [primaryMixedLift,ite_eq_left hx,ite_eq_left hy]
    rw [hnorm,← hu]
    apply mixedCubic_congr
    rw [map_mul,map_mul,hq]
  · have hy : ¬ IsUnit (Ideal.Quotient.mk (modulus 3) y) := by simpa only [← h3] using hx
    simp only [primaryMixedLift,ite_eq_right hx,ite_eq_right hy]

lemma primaryMixedLift_congr {a b x y : Eisenstein}
    (h : Ideal.Quotient.mk (modulus (3*(a*b))) x =
      Ideal.Quotient.mk (modulus (3*(a*b))) y) :
    primaryMixedLift a b x = primaryMixedLift a b y := by
  have hd : 3*(a*b) ∣ x-y := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  apply primaryMixedLift_congr_parts
  · exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr ((dvd_mul_right 3 (a*b)).trans hd))
  · exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr ((dvd_mul_left (a*b) 3).trans hd))

lemma primaryMixedLift_nonunit {a b x : Eisenstein} (ha : primary a) (hb : primary b)
    (hx : ¬ IsUnit (Ideal.Quotient.mk (modulus (3*(a*b))) x)) :
    primaryMixedLift a b x = 0 := by
  by_cases h3 : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · have hq : ¬ IsUnit (Ideal.Quotient.mk (modulus (a*b)) x) := by
      intro hq
      exact hx (residue_isUnit_of_isCoprime
        ((isCoprime_of_residue_isUnit h3).mul_left (isCoprime_of_residue_isUnit hq)))
    rw [primaryMixedLift,ite_eq_left h3]
    apply mixedCubic_eq_zero_of_nonunit ha hb
    intro hn
    obtain ⟨u,hu⟩ := primaryNormalize_associated x
    rw [← hu,map_mul,IsUnit.mul_iff] at hn
    exact hq hn.1
  · simp only [primaryMixedLift,ite_eq_right h3]

/-- The finite residue character agrees with the actual mixed cubic
symbol on primary elements and is trivial on global units. It may still
be imprimitive; conductor reduction is a separate step. -/
def primaryMixedResidueChar (a b : Eisenstein) (ha : primary a) (hb : primary b) :
    MulChar (Residues (3*(a*b))) ℂ where
  toFun v := primaryMixedLift a b (residueRepresentative (3*(a*b)) v)
  map_one' := by
    rw [primaryMixedLift_congr (show
      Ideal.Quotient.mk (modulus (3*(a*b))) (residueRepresentative (3*(a*b)) 1) =
        Ideal.Quotient.mk (modulus (3*(a*b))) 1 by rw [residueRepresentative_spec,map_one])]
    exact primaryMixedLift_one ha hb
  map_mul' v w := by
    rw [primaryMixedLift_congr (show
      Ideal.Quotient.mk (modulus (3*(a*b))) (residueRepresentative (3*(a*b)) (v*w)) =
        Ideal.Quotient.mk (modulus (3*(a*b)))
          (residueRepresentative (3*(a*b)) v*residueRepresentative (3*(a*b)) w) by
            rw [map_mul,residueRepresentative_spec,residueRepresentative_spec,residueRepresentative_spec])]
    exact primaryMixedLift_mul ha hb _ _
  map_nonunit' v hv := primaryMixedLift_nonunit ha hb (by rwa [residueRepresentative_spec])

@[simp] lemma primaryMixedResidueChar_mk {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (x : Eisenstein) :
    primaryMixedResidueChar a b ha hb (Ideal.Quotient.mk (modulus (3*(a*b))) x) =
      primaryMixedLift a b x := primaryMixedLift_congr (residueRepresentative_spec _ _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeckeCharacter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite factor at 3 required by a fixed angular Hecke character.
The archimedean phase is retained separately, including after primitive
conductor reduction. Complete ideal sums therefore include every prime
at which the primitive character is unramified. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

instance instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein : Nontrivial (Residues (3 : Eisenstein)) := residue_three_nontrivial

lemma theta_ne_zero {x : Eisenstein} (hx : x ≠ 0) (ℓ : ℤ) : theta ℓ x ≠ 0 := by
  intro h
  have hn := norm_theta hx ℓ
  rw [h, norm_zero] at hn
  norm_num at hn

lemma ne_zero_of_three_unit {x : Eisenstein}
    (hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)) : x ≠ 0 := by
  intro h
  simpa [h] using hx.ne_zero

/-- On elements prime to 3 this is precisely the unit correction
`theta_l(primaryNormalize x) / theta_l(x)`. It vanishes at the ramified
prime; it is a finite character, not an additional archimedean phase. -/
def angularUnitCorrection (ℓ : ℤ) (x : Eisenstein) : ℂ :=
  if IsUnit (Ideal.Quotient.mk (modulus 3) x) then
    theta ℓ (primaryNormalize x) / theta ℓ x else 0

lemma angularUnitCorrection_one (ℓ : ℤ) : angularUnitCorrection ℓ 1 = 1 := by
  simp [angularUnitCorrection, primaryNormalize_eq_self (show primary 1 by simp [primary])]

lemma angularUnitCorrection_mul (ℓ : ℤ) (x y : Eisenstein) :
    angularUnitCorrection ℓ (x*y) = angularUnitCorrection ℓ x*angularUnitCorrection ℓ y := by
  by_cases hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · by_cases hy : IsUnit (Ideal.Quotient.mk (modulus 3) y)
    · simp only [angularUnitCorrection, map_mul, IsUnit.mul_iff, hx, hy,
        and_self, ite_true, if_true, primaryNormalize_mul_of_residue_units hx hy, theta_mul]
      exact mul_div_mul_comm _ _ _ _
    · simp [angularUnitCorrection, map_mul, IsUnit.mul_iff, hx, hy]
  · simp [angularUnitCorrection, map_mul, IsUnit.mul_iff, hx]

lemma angularUnitCorrection_congr (ℓ : ℤ) {x y : Eisenstein}
    (h3 : Ideal.Quotient.mk (modulus 3) x = Ideal.Quotient.mk (modulus 3) y) :
    angularUnitCorrection ℓ x = angularUnitCorrection ℓ y := by
  by_cases hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · have hy : IsUnit (Ideal.Quotient.mk (modulus 3) y) := h3 ▸ hx
    obtain ⟨u,hu⟩ := primaryNormalize_associated x
    have hp : primary (y*(u:Eisenstein)) := by
      apply (primary_iff_residue_one _).mpr
      rw [map_mul, ←h3, ←map_mul, hu]
      exact (primary_iff_residue_one _).mp (primaryNormalize_primary hx)
    have he : primaryNormalize y = y*(u:Eisenstein) :=
      primary_associated_eq (primaryNormalize_primary hy) hp
        ((primaryNormalize_associated y).symm.trans ⟨u,rfl⟩)
    simp only [angularUnitCorrection, ite_eq_left hx, ite_eq_left hy, he, ←hu, theta_mul]
    rw [mul_div_cancel_left₀ _ (theta_ne_zero (ne_zero_of_three_unit hx) ℓ),
      mul_div_cancel_left₀ _ (theta_ne_zero (ne_zero_of_three_unit hy) ℓ)]
  · have hy : ¬ IsUnit (Ideal.Quotient.mk (modulus 3) y) := by
      simpa only [←h3] using hx
    simp [angularUnitCorrection, hx, hy]

/-- The correction is literally a multiplicative residue character
modulo 3. Thus its conductor divides 3. -/
def angularCorrectionChar (ℓ : ℤ) : MulChar (Residues (3 : Eisenstein)) ℂ where
  toFun v := angularUnitCorrection ℓ (residueRepresentative 3 v)
  map_one' := by
    rw [angularUnitCorrection_congr ℓ (show
      Ideal.Quotient.mk (modulus 3) (residueRepresentative 3 1) =
        Ideal.Quotient.mk (modulus 3) 1 by rw [residueRepresentative_spec, map_one])]
    exact angularUnitCorrection_one ℓ
  map_mul' v w := by
    rw [angularUnitCorrection_congr ℓ (show
      Ideal.Quotient.mk (modulus 3) (residueRepresentative 3 (v*w)) =
        Ideal.Quotient.mk (modulus 3) (residueRepresentative 3 v*residueRepresentative 3 w)
          by rw [map_mul, residueRepresentative_spec, residueRepresentative_spec,
            residueRepresentative_spec])]
    exact angularUnitCorrection_mul ℓ _ _
  map_nonunit' v hv := by
    simp only [angularUnitCorrection, residueRepresentative_spec, ite_eq_right hv]

@[simp] lemma angularCorrectionChar_mk (ℓ : ℤ) (x : Eisenstein) :
    angularCorrectionChar ℓ (Ideal.Quotient.mk (modulus 3) x) =
      angularUnitCorrection ℓ x :=
  angularUnitCorrection_congr ℓ (residueRepresentative_spec _ _)

/-- The correct unit condition for infinity type `ell`. For `ell=0`
it reduces to triviality on global units. -/
def AngularUnitCompatible (q : Eisenstein) (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) : Prop :=
  ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u)*theta ℓ u = 1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual short Möbius, zeta and logarithmic factors occurring in
the finite ideal convolution identity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def ShortArithmeticFactor (F : ℝ) (A : EisensteinArithmeticFunction) : Prop :=
  A = shortIdealMoebius F ∨ A = idealZeta ∨ A = idealLogNorm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorLargeValues
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual large-value rows for the short ideal factors. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- The arithmetic data of the actual short factors, before choosing a
set of characters on which their values are large. -/
structure ShortFactorFamily (ι : Type*) where
  cutoff : ℕ → ℝ
  length : ℕ → ι → ℝ
  coefficient : ℕ → ι → EisensteinArithmeticFunction
  twist : ℕ → ι → Eisenstein → ℂ
  factor_spec : ∀ j i, ShortArithmeticFactor (cutoff j) (coefficient j i)
  length_ge_one : ∀ j i, 1 ≤ length j i
  twist_bound : ∀ j i, ∀ a ∈ primaryElementBall (length j i), ‖twist j i a‖ ≤ 1

def ShortFactorFamily.cubicValue {ι : Type*} (F : ShortFactorFamily ι)
    (j : ℕ) (i : ι) (a : Eisenstein) : ℂ :=
  primaryIdealPolynomial (F.length j i) (F.coefficient j i)
    (fun n => F.twist j i n*cubicSymbol a n)

def ShortFactorFamily.mixedValue {ι : Type*} (F : ShortFactorFamily ι)
    (j : ℕ) (i : ι) (p : Eisenstein × Eisenstein) : ℂ :=
  primaryIdealPolynomial (F.length j i) (F.coefficient j i)
    (fun n => F.twist j i n*mixedCubic p.1 p.2 n)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorSequences
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual all-short families cannot have an unsaved moment sequence. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def ShortFactorFamily.comp {ι : Type*} (F : ShortFactorFamily ι) (φ : ℕ → ℕ) :
    ShortFactorFamily ι where
  cutoff := F.cutoff ∘ φ
  length := F.length ∘ φ
  coefficient := F.coefficient ∘ φ
  twist := F.twist ∘ φ
  factor_spec := fun j i => F.factor_spec (φ j) i
  length_ge_one := fun j i => F.length_ge_one (φ j) i
  twist_bound := fun j i => F.twist_bound (φ j) i

@[simp] lemma ShortFactorFamily.comp_cubicValue {ι : Type*} (F : ShortFactorFamily ι)
    (φ : ℕ → ℕ) (j : ℕ) (i : ι) (x : Eisenstein) :
    (F.comp φ).cubicValue j i x = F.cubicValue (φ j) i x := rfl

@[simp] lemma ShortFactorFamily.comp_mixedValue {ι : Type*} (F : ShortFactorFamily ι)
    (φ : ℕ → ℕ) (j : ℕ) (i : ι) (x : Eisenstein × Eisenstein) :
    (F.comp φ).mixedValue j i x = F.mixedValue (φ j) i x := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorUniform
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform power saving from the proved actual-sequence contradictions. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

structure ShortMomentInstance (ι κ : Type*) where
  scale : ℝ
  family : ShortFactorFamily ι
  rows : Finset κ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ConductorNeighborhoods
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform exceptional moments hold throughout a fixed open neighborhood
of each exceptional conductor exponent. The neighborhoods are constructed by
contradiction from actual short-factor sequences, not assumed as analytic inputs. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

structure ConductorMomentInstance (ι κ : Type*) extends ShortMomentInstance ι κ where
  conductorScale : ℝ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueProducts
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Products of the actual finite residue characters, including overlapping
moduli. The ideal coefficients are exactly the products of the two factors. -/
noncomputable section
namespace CubicFirstMoment

def residueProductLift {q r : Eisenstein} (χ : MulChar (Residues q) ℂ)
    (η : MulChar (Residues r) ℂ) (x : Eisenstein) : ℂ :=
  χ (Ideal.Quotient.mk (modulus q) x)*η (Ideal.Quotient.mk (modulus r) x)

lemma residueProductLift_congr {q r x y : Eisenstein}
    (χ : MulChar (Residues q) ℂ) (η : MulChar (Residues r) ℂ)
    (h : Ideal.Quotient.mk (modulus (q*r)) x = Ideal.Quotient.mk (modulus (q*r)) y) :
    residueProductLift χ η x = residueProductLift χ η y := by
  have hd : q*r ∣ x-y := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  unfold residueProductLift
  rw [residue_eq_of_dvd_sub ((dvd_mul_right q r).trans hd),
    residue_eq_of_dvd_sub ((dvd_mul_left r q).trans hd)]

lemma residueProductLift_mul {q r : Eisenstein} (χ : MulChar (Residues q) ℂ)
    (η : MulChar (Residues r) ℂ) (x y : Eisenstein) :
    residueProductLift χ η (x*y) = residueProductLift χ η x*residueProductLift χ η y := by
  simp only [residueProductLift,map_mul]
  ring

lemma residueProductLift_nonunit {q r x : Eisenstein} (χ : MulChar (Residues q) ℂ)
    (η : MulChar (Residues r) ℂ) (hx : ¬ IsUnit (Ideal.Quotient.mk (modulus (q*r)) x)) :
    residueProductLift χ η x = 0 := by
  by_cases hq : IsUnit (Ideal.Quotient.mk (modulus q) x)
  · have hr : ¬ IsUnit (Ideal.Quotient.mk (modulus r) x) := by
      intro hr
      exact hx (residue_isUnit_of_isCoprime
        ((isCoprime_of_residue_isUnit hq).mul_left (isCoprime_of_residue_isUnit hr)))
    simp only [residueProductLift,MulChar.map_nonunit η hr,mul_zero]
  · simp only [residueProductLift,MulChar.map_nonunit χ hq,zero_mul]

def productResidueChar {q r : Eisenstein} (χ : MulChar (Residues q) ℂ)
    (η : MulChar (Residues r) ℂ) : MulChar (Residues (q*r)) ℂ where
  toFun x := residueProductLift χ η (residueRepresentative (q*r) x)
  map_one' := by
    rw [residueProductLift_congr χ η (show
      Ideal.Quotient.mk (modulus (q*r)) (residueRepresentative (q*r) 1) =
      Ideal.Quotient.mk (modulus (q*r)) 1 by rw [residueRepresentative_spec,map_one])]
    simp only [residueProductLift,map_one,mul_one]
  map_mul' x y := by
    rw [residueProductLift_congr χ η (show
      Ideal.Quotient.mk (modulus (q*r)) (residueRepresentative (q*r) (x*y)) =
      Ideal.Quotient.mk (modulus (q*r))
        (residueRepresentative (q*r) x*residueRepresentative (q*r) y) by
          rw [map_mul,residueRepresentative_spec,residueRepresentative_spec,residueRepresentative_spec])]
    exact residueProductLift_mul χ η _ _
  map_nonunit' x hx := residueProductLift_nonunit χ η (by rwa [residueRepresentative_spec])

@[simp] lemma productResidueChar_mk {q r : Eisenstein} (χ : MulChar (Residues q) ℂ)
    (η : MulChar (Residues r) ℂ) (x : Eisenstein) :
    productResidueChar χ η (Ideal.Quotient.mk (modulus (q*r)) x) =
      χ (Ideal.Quotient.mk (modulus q) x)*η (Ideal.Quotient.mk (modulus r) x) :=
  residueProductLift_congr χ η (residueRepresentative_spec _ _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicNumeratorCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite numerator character needed for arbitrary v in the
exceptional moments. The only conditional input here is the periodicity
consequence of cubic reciprocity and the unit/ramified supplementary laws:
Dunn–Radziwiłł (2024), equations (1.4)–(1.5). -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Cubic reciprocity plus its supplementary laws, specialized to
periodicity of the actual cubic symbol on primary denominators. -/
def CubicSupplementaryPeriodicity : Prop :=
  ∀ v : Eisenstein, v ≠ 0 → ∀ a b : Eisenstein,
    primary a → primary b → (9*v) ∣ a-b → cubicSymbol a v = cubicSymbol b v

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicSupplementaryPeriodicityProof
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Modulo `9v` periodicity of the actual cubic numerator symbol.

The ramified factor is treated by reciprocity against an auxiliary primary
argument. The unit factor follows from Euler's finite-field definition. This
proves the elementary specialization recorded in DR v3, §1.2 (1.4)--(1.5),
including the zero values at common prime factors. -/
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma omega_ne_zero : omega ≠ 0 := omega_primitive.ne_zero (by decide)

lemma primary_coprime_three' {a : Eisenstein} (ha : primary a) :
    IsCoprime a 3 := by
  obtain ⟨k, hk⟩ := ha
  exact ⟨1, -k, by linear_combination hk⟩

/-- Reciprocity compares the value at three whenever both quotients are primary. -/
lemma symbol_three_aux {a r x : Eisenstein}
    (ha : primary a) (hr : primary r) (hx : primary x)
    (hax : a - r = 3*x) (har : IsCoprime a r) :
    cubicSymbol a 3 = cubicSymbol r 3 := by
  have hrx : IsCoprime r x := by
    have h : IsCoprime r (3*x + r*1) := by
      rw [show 3*x + r*1 = a by linear_combination -hax]
      exact har.symm
    exact h.of_add_mul_left_right.of_mul_right_right
  have hn : cubicSymbol r x ≠ 0 := by
    intro hz
    have hh := norm_cubicSymbol_of_isCoprime hr hrx
    rw [hz, norm_zero] at hh
    norm_num at hh
  have hleft : cubicSymbol a (3*x) = cubicSymbol a (-r) :=
    cubicSymbol_congr (residue_eq_of_dvd_sub ⟨1, by linear_combination -hax⟩)
  have hright : cubicSymbol r a = cubicSymbol r (3*x) :=
    cubicSymbol_congr (residue_eq_of_dvd_sub ⟨1, by linear_combination hax⟩)
  rw [cubicSymbol_mul_upper ha, cubicSymbol_neg ha,
    cubic_reciprocity ha hr, hright, cubicSymbol_mul_upper hr] at hleft
  have hxa : cubicSymbol x a = cubicSymbol x r :=
    cubicSymbol_congr (residue_eq_of_dvd_sub ⟨3, by linear_combination hax⟩)
  rw [cubic_reciprocity ha hx,hxa,cubic_reciprocity hx hr] at hleft
  exact mul_right_cancel₀ hn hleft

/-- The ramified supplementary factor depends only on the primary argument modulo nine. -/
lemma cubicSymbol_three_periodic {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hab : (9 : Eisenstein) ∣ a-b) : cubicSymbol a 3 = cubicSymbol b 3 := by
  obtain ⟨d, hd⟩ := hab
  obtain ⟨s, t, ht⟩ := (primary_coprime_three' hb).pow_right (n := 2)
  have ht' : s*b + t*9 = 1 := by convert ht using 1; norm_num
  let r := a - 3 - 9*a*t
  let x := 1 + 3*a*t
  let y := x - 3*d
  have hr : primary r := by
    obtain ⟨k,hk⟩ := ha
    exact ⟨k - 1 - 3*a*t, by dsimp [r]; linear_combination hk⟩
  have hx : primary x := ⟨a*t, by dsimp [x]; ring⟩
  have hy : primary y := ⟨a*t-d, by dsimp [y,x]; ring⟩
  have har : IsCoprime a r := by
    obtain ⟨u,v,hv⟩ := primary_coprime_three' ha
    refine ⟨u + v*(1-9*t), -v, ?_⟩
    dsimp [r]
    linear_combination hv
  have hbr : IsCoprime b r := by
    obtain ⟨u,v,hv⟩ := primary_coprime_three' hb
    refine ⟨u + v*a*s, -v, ?_⟩
    dsimp [r]
    linear_combination hv + v*a*ht'
  have hax : a-r = 3*x := by dsimp [r,x]; ring
  have hby : b-r = 3*y := by dsimp [r,y,x]; linear_combination -hd
  exact (symbol_three_aux ha hr hx hax har).trans
    (symbol_three_aux hb hr hy hby hbr).symm

lemma cubicSymbol_lambda_periodic {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hab : (9 : Eisenstein) ∣ a-b) : cubicSymbol a lambdaE = cubicSymbol b lambdaE := by
  have he := cubicSymbol_three_periodic ha hb hab
  have hsa : cubicSymbol a 3 = cubicSymbol a lambdaE ^ 2 := by
    rw [← neg_neg (3 : Eisenstein), ← lambdaE_sq, cubicSymbol_neg ha,
      cubicSymbol_pow_upper ha]
  have hsb : cubicSymbol b 3 = cubicSymbol b lambdaE ^ 2 := by
    rw [← neg_neg (3 : Eisenstein), ← lambdaE_sq, cubicSymbol_neg hb,
      cubicSymbol_pow_upper hb]
  rw [hsa,hsb] at he
  have hca := cubicSymbol_cube_of_isCoprime ha lambdaE (primary_coprime_lambda ha)
  have hcb := cubicSymbol_cube_of_isCoprime hb lambdaE (primary_coprime_lambda hb)
  calc
    cubicSymbol a lambdaE = (cubicSymbol a lambdaE ^ 2)^2 := by
      calc
        _ = cubicSymbol a lambdaE * cubicSymbol a lambdaE ^ 3 := by rw [hca,mul_one]
        _ = _ := by ring
    _ = (cubicSymbol b lambdaE ^ 2)^2 := congrArg (· ^ 2) he
    _ = cubicSymbol b lambdaE := by
      calc
        _ = cubicSymbol b lambdaE * cubicSymbol b lambdaE ^ 3 := by ring
        _ = _ := by rw [hcb,mul_one]

lemma normNat_int (a : Eisenstein) : (normNat a : ℤ) = Algebra.norm ℤ a := by
  apply Int.cast_injective (α := ℝ)
  simpa only [Int.cast_natCast, normNat_cast] using (algebra_norm_cast a).symm

lemma primary_norm_third {a : Eisenstein} (ha : primary a) :
    ∃ k : ℤ, (normNat a : ℤ) = 3*k+1 := by
  obtain ⟨z,hz⟩ := ha
  obtain ⟨⟨x,y⟩,rfl⟩ := ofCoords_surjective z
  have he : a = ofCoords (1+3*x) (3*y) := by
    dsimp only [ofCoords] at hz ⊢
    push_cast
    linear_combination hz
  rw [normNat_int,he,algebra_norm_ofCoords]
  refine ⟨2*x-y+3*(x^2-x*y+y^2),?_⟩
  ring

lemma symbol_omega_prime {p : Eisenstein} (hp : primaryPrime p) :
    cubicSymbol p omegaE = omega ^ ((normNat p-1)/3) := by
  let k := (normNat p-1)/3
  let j : Fin 3 := ⟨k%3, Nat.mod_lt _ (by decide)⟩
  have he : omegaE^(j : ℕ) = omegaE^k := by
    change omegaE ^ (k%3) = _
    simpa only [← omegaE_primitive.eq_orderOf] using pow_mod_orderOf omegaE k
  rw [cubicSymbol_prime hp]
  have hu : IsUnit (Ideal.Quotient.mk (modulus p) omegaE) :=
    omegaE_isUnit.map (Ideal.Quotient.mk (modulus p))
  rw [cubicSymbol_euler_value hp hu j (congrArg (Ideal.Quotient.mk (modulus p)) he.symm)]
  change omega^(k%3) = omega^k
  simpa only [← omega_primitive.eq_orderOf] using pow_mod_orderOf omega k

/-- Euler's definition for the unit factor, with an integer exponent convenient for congruences. -/
lemma cubicSymbol_omega_norm {a : Eisenstein} (ha : primary a) :
    cubicSymbol a omegaE = omega ^ (((normNat a : ℤ)-1)/3) := by
  apply primary_induction (b := a) ?_ ?_ ha
  · norm_num [cubicSymbol_one_lower, normNat_of_isUnit isUnit_one]
  · intro p a hp ha ih
    obtain ⟨j,hj⟩ := primary_norm_third hp.1
    obtain ⟨k,hk⟩ := primary_norm_third ha
    have hpN : 1 ≤ normNat p := Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero hp.2.ne_zero)
    have hcast : (((normNat p-1)/3 : ℕ) : ℤ) = j := by
      rw [Int.natCast_div, Int.natCast_sub hpN,hj]
      omega
    rw [cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero ha), symbol_omega_prime hp, ih,
      ← zpow_natCast, hcast, normNat_mul, Nat.cast_mul, hj,hk]
    have hdiv : (((3*j+1)*(3*k+1)-1)/3 : ℤ) = j+k+3*(j*k) := by
      apply Int.ediv_eq_of_eq_mul_right (by decide : (3 : ℤ) ≠ 0)
      ring
    have hdk : (3*k+1-1)/3 = k := by omega
    rw [hdk,hdiv,zpow_add₀ omega_ne_zero,zpow_add₀ omega_ne_zero,
      zpow_mul,show omega ^ (3 : ℤ) = 1 by simpa using omega_cube,one_zpow,mul_one]

lemma cubicSymbol_omega_periodic {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hab : (9 : Eisenstein) ∣ a-b) : cubicSymbol a omegaE = cubicSymbol b omegaE := by
  obtain ⟨d,hd⟩ := hab
  obtain ⟨⟨x,y⟩,he⟩ := ofCoords_surjective b
  obtain ⟨⟨z,w⟩,hf⟩ := ofCoords_surjective d
  have ha' : a = ofCoords (x+9*z) (y+9*w) := by
    rw [← he,← hf] at hd
    dsimp only [ofCoords] at hd ⊢
    push_cast
    linear_combination hd
  have hn : (9 : ℤ) ∣ (normNat a : ℤ) - normNat b := by
    rw [normNat_int,normNat_int,ha',← he,algebra_norm_ofCoords,algebra_norm_ofCoords]
    refine ⟨2*x*z-x*w-z*y+2*y*w+9*(z^2-z*w+w^2),?_⟩
    ring
  obtain ⟨j,hj⟩ := primary_norm_third ha
  obtain ⟨k,hk⟩ := primary_norm_third hb
  obtain ⟨t,ht⟩ := hn
  have hjk : j = k+3*t := by omega
  rw [cubicSymbol_omega_norm ha,cubicSymbol_omega_norm hb,hj,hk]
  have hdj : (3*j+1-1)/3 = j := by omega
  have hdk : (3*k+1-1)/3 = k := by omega
  rw [hdj,hdk,hjk,zpow_add₀ omega_ne_zero,zpow_mul,
    show omega ^ (3 : ℤ) = 1 by simpa using omega_cube,one_zpow,mul_one]

lemma unit_eq_signed_omega {u : Eisenstein} (hu : IsUnit u) :
    ∃ j : ℕ, u = omegaE^j ∨ u = -(omegaE^j) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := ofCoords_surjective u
  have hn : a^2-a*b+b^2 = 1 := by
    have hh := norm_of_isUnit hu
    rw [norm,ofCoords_coe,coordinates_norm] at hh
    exact_mod_cast hh
  have ha : -1 ≤ a ∧ a ≤ 1 := by
    constructor
    · by_contra h
      have hh : a ≤ -2 := by omega
      nlinarith [sq_nonneg (a-2*b)]
    · by_contra h
      have hh : 2 ≤ a := by omega
      nlinarith [sq_nonneg (a-2*b)]
  have hb : -1 ≤ b ∧ b ≤ 1 := by
    constructor
    · by_contra h
      have hh : b ≤ -2 := by omega
      nlinarith [sq_nonneg (2*a-b)]
    · by_contra h
      have hh : 2 ≤ b := by omega
      nlinarith [sq_nonneg (2*a-b)]
  obtain ⟨ha0,ha1⟩ := ha
  obtain ⟨hb0,hb1⟩ := hb
  interval_cases a <;> interval_cases b <;> norm_num at hn
  · exact ⟨2, Or.inl (by dsimp [ofCoords]; push_cast; linear_combination -omegaE_quadratic)⟩
  · exact ⟨0, Or.inr (by norm_num [ofCoords])⟩
  · exact ⟨1, Or.inr (by norm_num [ofCoords])⟩
  · exact ⟨1, Or.inl (by norm_num [ofCoords])⟩
  · exact ⟨0, Or.inl (by norm_num [ofCoords])⟩
  · exact ⟨2, Or.inr (by dsimp [ofCoords]; push_cast; linear_combination omegaE_quadratic)⟩

lemma cubicSymbol_unit_periodic {a b u : Eisenstein} (ha : primary a) (hb : primary b)
    (hu : IsUnit u) (hab : (9 : Eisenstein) ∣ a-b) :
    cubicSymbol a u = cubicSymbol b u := by
  obtain ⟨j,hj | hj⟩ := unit_eq_signed_omega hu
  · rw [hj,cubicSymbol_pow_upper ha,cubicSymbol_pow_upper hb,
      cubicSymbol_omega_periodic ha hb hab]
  · rw [hj,cubicSymbol_neg ha,cubicSymbol_neg hb,cubicSymbol_pow_upper ha,
      cubicSymbol_pow_upper hb,cubicSymbol_omega_periodic ha hb hab]

lemma unit_coprime_right (b : Eisenstein) {u : Eisenstein} (hu : IsUnit u) :
    IsCoprime b u := by
  obtain ⟨z,hz⟩ := isUnit_iff_exists_inv'.mp hu
  exact ⟨0,z,by simpa only [zero_mul,zero_add] using hz⟩

lemma normNat_lambda : normNat lambdaE = 3 := by
  have hh := congrArg normNat lambdaE_sq
  rw [pow_two,normNat_mul] at hh
  have hn : normNat (-3 : Eisenstein) = 9 := by
    apply Nat.cast_injective (R := ℝ)
    rw [normNat_cast]
    change Complex.normSq (-(3 : ℂ)) = 9
    norm_num [Complex.normSq_apply]
  rw [hn] at hh
  nlinarith

lemma lambda_irreducible : Irreducible lambdaE := by
  refine ⟨?_,?_⟩
  · intro hu
    have hh := normNat_of_isUnit hu
    rw [normNat_lambda] at hh
    norm_num at hh
  · intro x y h
    have hh : normNat x * normNat y = 3 := by rw [← normNat_mul,← h,normNat_lambda]
    have hor := (show Irreducible (3 : ℕ) from Nat.prime_three).isUnit_or_isUnit hh.symm
    have reflect {z : Eisenstein} (hz : IsUnit (normNat z)) : IsUnit z := by
      apply isUnit_of_norm_eq_one
      rw [← normNat_cast,Nat.isUnit_iff.mp hz]
      norm_num
    exact hor.imp reflect reflect

lemma lambdaE_prime : Prime lambdaE := irreducible_iff_prime.mp lambda_irreducible

/-- All nonzero numerators, with the usual zero extension at common factors. -/
theorem cubicSupplementaryPeriodicity_proved : CubicSupplementaryPeriodicity := by
  intro v hv
  have main : ∀ v : Eisenstein, v ≠ 0 → ∀ a b : Eisenstein,
      primary a → primary b → (9*v) ∣ a-b → cubicSymbol a v = cubicSymbol b v := by
    intro v
    induction v using WfDvdMonoid.induction_on_irreducible with
    | zero => simp
    | unit u hu =>
      intro _ a b ha hb hab
      exact cubicSymbol_unit_periodic ha hb hu ((dvd_mul_right 9 u).trans hab)
    | mul v p hv hp ih =>
      intro _ a b ha hb hab
      have h9 : (9 : Eisenstein) ∣ a-b := (dvd_mul_right 9 (p*v)).trans hab
      rw [cubicSymbol_mul_upper ha,cubicSymbol_mul_upper hb]
      congr 1
      · by_cases hp3 : IsCoprime p 3
        · obtain ⟨u,hu,hprim⟩ := unit_lift_mod_three (residue_isUnit_of_isCoprime hp3.symm)
          have heA : cubicSymbol a (p*u) = cubicSymbol (p*u) a := cubic_reciprocity ha hprim
          have heB : cubicSymbol b (p*u) = cubicSymbol (p*u) b := cubic_reciprocity hb hprim
          have hpv : p ∣ a-b := (dvd_mul_right p v).trans
            ((dvd_mul_left (p*v) 9).trans hab)
          have hpu : p*u ∣ a-b := by
            exact (associated_mul_unit_right p u hu).dvd_iff_dvd_left.mp hpv
          have heq := cubicSymbol_congr (b := p*u) (residue_eq_of_dvd_sub hpu)
          rw [cubicSymbol_mul_upper ha] at heA
          rw [cubicSymbol_mul_upper hb] at heB
          have huu := cubicSymbol_unit_periodic ha hb hu h9
          rw [← heA,← heB,huu] at heq
          apply mul_right_cancel₀ _ heq
          intro hz
          have hnorm := norm_cubicSymbol_of_isCoprime hb
            (show IsCoprime b u from unit_coprime_right b hu)
          rw [hz,norm_zero] at hnorm
          norm_num at hnorm
        · have hpd : p ∣ (3 : Eisenstein) := by
            by_contra h
            exact hp3 (isRelPrime_iff_isCoprime.mp (hp.isRelPrime_iff_not_dvd.mpr h))
          have hpl : p ∣ lambdaE := hp.prime.dvd_of_dvd_pow
            (by rw [lambdaE_sq]; exact dvd_neg.mpr hpd)
          have hpunit : Associated p lambdaE :=
            (hp.associated_of_dvd lambda_irreducible hpl)
          obtain ⟨u,hu⟩ := hpunit
          have hunit := cubicSymbol_unit_periodic ha hb u.isUnit h9
          have hlam := cubicSymbol_lambda_periodic ha hb h9
          have he : cubicSymbol a (p*(u : Eisenstein)) =
              cubicSymbol b (p*(u : Eisenstein)) := by simpa only [hu] using hlam
          rw [cubicSymbol_mul_upper ha,cubicSymbol_mul_upper hb,hunit] at he
          apply mul_right_cancel₀ _ he
          intro hz
          have hnorm := norm_cubicSymbol_of_isCoprime hb (unit_coprime_right b u.isUnit)
          rw [hz,norm_zero] at hnorm
          norm_num at hnorm
      · apply ih hv a b ha hb
        apply dvd_trans _ hab
        refine ⟨p,?_⟩
        ring
  exact main v hv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FixedAngularHecke
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative fixed-angular Hecke prime estimates

The published input is the degree-two, nonexceptional specialization of
Kaneko--Thorner, *Highly uniform prime number theorems*, Ann. Inst. Fourier
75 (2025), Theorem 1.2, pp. 1904--1905 (restating Iwaniec--Kowalski,
Theorem 5.13), with the zero-free region and completion from Rajan (1998),
Proposition 1 and Section 1. The exponential conductor-dependent error
is retained. Arbitrary logarithmic savings are derived below; they are
not included among the published-input hypotheses.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped BigOperators

namespace CubicFirstMoment

/-- The logarithmically weighted sum over the actual primary prime elements. -/
def primeChebyshev (ψ : Eisenstein → ℂ) (x : ℝ) : ℂ :=
  primeCutoffSum (fun p => ψ p * (Real.log (norm p) : ℂ)) x

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeCompletedOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Classical order-one completion as the weak analytic input.
Thorner--Zaman, ANT 13 (2019), §2C, p.1049, Eq. (2-15), states
that the completed primitive nonprincipal Hecke function is entire of
order one. The coarse quadratic exponential majorant below is sufficient.
The reciprocal Gamma strip bound is a weak consequence of the uniform
vertical Stirling formula, DLMF 5.11.9, and its entire reciprocal (5.2.2).
These inputs concern individual analytic functions, not arithmetic means. -/

noncomputable section
open Set
namespace CubicFirstMoment

/-- An order-one completed function has this deliberately coarse
quadratic exponential bound. The regular-point equality respects Lean's
zero-valued Gamma at its poles. -/
def CompletedHeckeFiniteOrder (A : ℝ) (L : ℂ → ℂ) : Prop :=
  ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
    (∀ s : ℂ, Complex.Gamma s ≠ 0 → Λ s = heckeCompleted A 0 L s) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖Λ s‖ ≤ Real.exp (C*(1+‖s‖)^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealDualDyads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact dyadic decomposition of the retained full-ideal polynomial.
The square-root normalization changes only coefficients, not characters. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def idealDyadIndex (ν : EisensteinIdealExponent) : ℕ :=
  Nat.log 2 (normNat (idealExponentGenerator ν))

def idealDyadIndices (S : Finset EisensteinIdealExponent) : Finset ℕ := S.image idealDyadIndex

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyLiftedPacking
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local multiplicity of the reduced fractions and all their lattice translates. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[ext] structure HuxleyLift where
  denominator : Eisenstein
  numerator : Eisenstein
  shift : Eisenstein
  deriving DecidableEq

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogReplacement
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact replacement of a prime indicator by von Mangoldt divided by log norm.
The discrepancy is bounded and is supported on actual higher primary prime powers. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primeIndicator (a : Eisenstein) : ℝ := if Prime a then 1 else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveResidueFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The perfect codifferent pairing on every Eisenstein residue ring.
Unlike the trace pairing without the different, this includes ramified moduli. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

/-- Canonical primitive additive character modulo any nonzero Eisenstein integer. -/
def residueFourierChar (q : Eisenstein) (hq : q ≠ 0) : AddChar (Residues q) ℂ where
  toFun a := Real.fourierChar (tracePair (residueRepresentative q a : ℂ)
    (1 / ((q : ℂ) * traceLambda)))
  map_zero_eq_one' := by
    have he := tracePhase_congr hq 1 (show
      Ideal.Quotient.mk (modulus q) (residueRepresentative q 0) =
        Ideal.Quotient.mk (modulus q) 0 by rw [residueRepresentative_spec, map_zero])
    simp only [Subalgebra.coe_one] at he
    rw [he]
    simp [tracePair]
  map_add_eq_mul' a b := by
    have he := tracePhase_congr hq 1 (show
      Ideal.Quotient.mk (modulus q) (residueRepresentative q (a+b)) =
        Ideal.Quotient.mk (modulus q) (residueRepresentative q a + residueRepresentative q b)
        by rw [map_add, residueRepresentative_spec, residueRepresentative_spec,
          residueRepresentative_spec])
    simp only [Subalgebra.coe_one] at he
    rw [he]
    simp only [Subalgebra.coe_add, tracePair_add_left, AddChar.map_add_eq_mul,
      Circle.coe_mul]

@[simp] lemma residueFourierChar_mk (q : Eisenstein) (hq : q ≠ 0) (a : Eisenstein) :
    residueFourierChar q hq (Ideal.Quotient.mk (modulus q) a) =
      (Real.fourierChar (tracePair (a : ℂ) (1 / ((q : ℂ) * traceLambda))) : ℂ) := by
  exact tracePhase_congr hq 1 (residueRepresentative_spec _ _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveResidueConductorKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitivity detects the kernel of every proper residue reduction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

/-- Reduction between actual Eisenstein residue rings. -/
def residueReduction {q d : Eisenstein} (hd : d ∣ q) : Residues q →+* Residues d :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr hd)

@[simp] lemma residueReduction_mk {q d : Eisenstein} (hd : d ∣ q) (x : Eisenstein) :
    residueReduction hd (Ideal.Quotient.mk (modulus q) x) =
      Ideal.Quotient.mk (modulus d) x := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedAngularKummerPrime
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed-angular prime estimates for the literal ramified numerator

This is the nonexceptional degree-two specialization of Kaneko--Thorner,
*Highly uniform prime number theorems*, Ann. Inst. Fourier 75 (2025),
Theorem 1.2, pp.1904--1905 (Iwaniec--Kowalski, Theorem 5.13), with the
fixed-type zero-free region of Rajan (1998), Proposition 1 and Section 1.
The finite character is `cubicNumeratorChar` of modulus `9*v`; its
identification on primary elements is proved from
`CubicSupplementaryPeriodicity` in `CubicNumeratorCharacter`.

The analytic conductor majorant is
`3 * N(9*v) * (|ell|/2+3) * (|ell|/2+4)`:
`N(9*v)=81*N(v)`, so its constant is 243. The nonzero angular type
excludes a principal/exceptional-real character. The raw input below
retains the exponential conductor error and the prime-power deletion
term. Logarithmic and weighted estimates are deductions, not inputs.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def angularKummerCharacter (ℓ : ℤ) (v p : Eisenstein) : ℂ :=
  theta ℓ p*cubicSymbol p v

def angularKummerAnalyticConductor (ℓ : ℤ) (v : Eisenstein) : ℝ :=
  angularKummerConductorFactor ℓ*norm v

/-- Precisely the raw fixed-angular prime Chebyshev estimate for the
finite numerator character, including ramification and unit factors.
No stopped-sequence, smooth-weight, or dispersion conclusion is assumed. -/
def AngularKummerPrimeExplicitEstimate : Prop :=
  ∀ ℓ : ℤ, ℓ ≠ 0 → ∃ B c : ℝ, 0 < B ∧ 0 < c ∧
    ∀ v : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      ∀ x : ℝ, 3 ≤ x →
        ‖primeChebyshev (angularKummerCharacter ℓ v) x‖ ≤
          B*(heckeExponentialError c x (angularKummerAnalyticConductor ℓ v)+
            Real.sqrt x*(Real.log x)^2)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RamifiedPrimaryDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of a nonzero Eisenstein integer into a global unit,
a ramified-prime power, and a primary factor. -/
noncomputable section
namespace CubicFirstMoment

lemma unit_ramified_primary_decomposition {v : Eisenstein} (hv : v ≠ 0) :
    ∃ (u : Eisensteinˣ) (k : ℕ) (a : Eisenstein), primary a ∧
      v=(u:Eisenstein)*lambdaE^k*a := by
  have H : ∀ v : Eisenstein, v ≠ 0 →
      ∃ (u : Eisensteinˣ) (k : ℕ) (a : Eisenstein), primary a ∧
        v=(u:Eisenstein)*lambdaE^k*a := by
    intro v
    induction v using WfDvdMonoid.induction_on_irreducible with
    | zero => simp
    | unit b hb =>
      intro _
      obtain ⟨u,rfl⟩ := hb
      exact ⟨u,0,1,primary_one,by simp⟩
    | mul b p hb hp ih =>
      intro _
      obtain ⟨u,k,a,ha,he⟩ := ih hb
      by_cases hp3 : IsCoprime p 3
      · obtain ⟨w,hw,hpw⟩ := unit_lift_mod_three (residue_isUnit_of_isCoprime hp3.symm)
        obtain ⟨w,rfl⟩ := hw
        refine ⟨u*w⁻¹,k,(p*(w:Eisenstein))*a,primary_mul hpw ha,?_⟩
        rw [he,Units.val_mul]
        linear_combination -(p*(u:Eisenstein)*lambdaE^k*a)*w.mul_inv
      · have hpd : p ∣ (3:Eisenstein) := by
          by_contra h
          exact hp3 (isRelPrime_iff_isCoprime.mp (hp.isRelPrime_iff_not_dvd.mpr h))
        have hpl : p ∣ lambdaE := hp.prime.dvd_of_dvd_pow
          (by rw [lambdaE_sq]; exact dvd_neg.mpr hpd)
        obtain ⟨w,hw⟩ := hp.associated_of_dvd lambdaE_prime.irreducible hpl
        refine ⟨u*w⁻¹,k+1,a,ha,?_⟩
        rw [he,Units.val_mul,pow_succ,←hw]
        linear_combination -(p*(u:Eisenstein)*(p*(w:Eisenstein))^k*a)*w.mul_inv
  exact H v hv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SchwartzLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Poisson proof of the lattice approximation needed by the cubic profile. -/

noncomputable section
open scoped BigOperators SchwartzMap
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma traceLambda_normSq : Complex.normSq traceLambda = 3 := by
  rw [traceLambda_eq,Complex.normSq_mul,Complex.normSq_ofReal]
  norm_num [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmetic
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized arithmetic coefficient of DR v3 (5.7), indexed on the
common cusp lattice lambda^-4 Z[omega]. The coefficient used in the
Whittaker series is tau(mu)/|mu|. No modular transformation is asserted. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[ext] structure CubicThetaCoordinates (n : Eisenstein) where
  unit : Eisensteinˣ
  order : ℕ
  squarefreePart : Eisenstein
  cubePart : Eisenstein
  squarefree_primary : primary squarefreePart
  cube_primary : primary cubePart
  squarefree : Squarefree squarefreePart
  numerator_eq : n = (unit:Eisenstein)*lambdaE^order*(squarefreePart*cubePart^3)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaKubotaValue
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual principal congruence group and pointwise cubic Kubota
multiplier of DR v3 (5.4). Multiplicativity and theta automorphy are not
assumed by these arithmetic definitions. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrincipalGroup : Subgroup SL(2,Eisenstein) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (modulus (3:Eisenstein)))).ker

lemma cubicThetaPrincipalGroup_diagonal_primary (g : cubicThetaPrincipalGroup) :
    primary (g.val 0 0) ∧ primary (g.val 1 1) := by
  have hm : Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (modulus (3:Eisenstein))) g.val = 1 :=
    g.property
  constructor
  · have he := congrArg (fun h : SL(2,Residues (3:Eisenstein)) => h 0 0) hm
    change Ideal.Quotient.mk (modulus (3:Eisenstein)) (g.val 0 0) = 1 at he
    have hz : Ideal.Quotient.mk (modulus (3:Eisenstein)) (g.val 0 0-1) = 0 := by
      rw [map_sub,map_one,he,sub_self]
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  · have he := congrArg (fun h : SL(2,Residues (3:Eisenstein)) => h 1 1) hm
    change Ideal.Quotient.mk (modulus (3:Eisenstein)) (g.val 1 1) = 1 at he
    have hz : Ideal.Quotient.mk (modulus (3:Eisenstein)) (g.val 1 1-1) = 0 := by
      rw [map_sub,map_one,he,sub_self]
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)

lemma cubicThetaPrincipalGroup_column_coprime (g : cubicThetaPrincipalGroup) :
    IsCoprime (g.val 0 0) (g.val 1 0) := by
  have hd : g.val 0 0*g.val 1 1-g.val 0 1*g.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.val.property
  refine ⟨g.val 1 1,-g.val 0 1,?_⟩
  linear_combination hd

/-- The cubic residue value in the original Kubota convention. -/
def cubicThetaKubotaValue (g : cubicThetaPrincipalGroup) : ℂ :=
  if g.val 1 0 = 0 then 1 else cubicSymbol (g.val 0 0) (g.val 1 0)

lemma cubicThetaKubotaValue_norm (g : cubicThetaPrincipalGroup) :
    ‖cubicThetaKubotaValue g‖ = 1 := by
  unfold cubicThetaKubotaValue
  split_ifs
  · simp
  · exact norm_cubicSymbol_of_isCoprime (cubicThetaPrincipalGroup_diagonal_primary g).1
      (cubicThetaPrincipalGroup_column_coprime g)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaKubotaSupplement
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary supplementary-law calculation used for the Kubota
multiplier in DR v3 Remark 5.1. -/
noncomputable section
namespace CubicFirstMoment

/-- The unit and ramified factors need only congruence modulo nine;
the primary factor needs congruence modulo the numerator itself. -/
lemma cubicSymbol_periodic_of_nine_and_numerator {a b c : Eisenstein}
    (ha : primary a) (hb : primary b) (h9 : (9:Eisenstein) ∣ a-b)
    (hc : c ∣ a-b) : cubicSymbol a c = cubicSymbol b c := by
  by_cases hc0 : c = 0
  · rw [hc0,zero_dvd_iff] at hc
    rw [sub_eq_zero.mp hc]
  · obtain ⟨u,k,d,hd,he⟩ := unit_ramified_primary_decomposition hc0
    have hdc : d ∣ c := by
      refine ⟨(u:Eisenstein)*lambdaE^k,?_⟩
      rw [he]
      ring
    have hds : cubicSymbol a d = cubicSymbol b d := by
      rw [cubic_reciprocity ha hd,cubic_reciprocity hb hd]
      exact cubicSymbol_congr (residue_eq_of_dvd_sub (dvd_trans hdc hc))
    rw [he,cubicSymbol_mul_upper ha,cubicSymbol_mul_upper ha,
      cubicSymbol_mul_upper hb,cubicSymbol_mul_upper hb,
      cubicSymbol_pow_upper ha,cubicSymbol_pow_upper hb,
      cubicSymbol_unit_periodic ha hb u.isUnit h9,
      cubicSymbol_lambda_periodic ha hb h9,hds]

/-- If a primary denominator is one modulo nine and modulo the numerator,
all unit, ramified and primary parts of its cubic residue value are one. -/
lemma cubicThetaKubota_symbol_one {D c : Eisenstein} (hD : primary D)
    (h9 : (9:Eisenstein) ∣ D-1) (hc : c ∣ D-1) : cubicSymbol D c = 1 := by
  by_cases hc0 : c = 0
  · rw [hc0,zero_dvd_iff] at hc
    have hD1 : D = 1 := sub_eq_zero.mp hc
    rw [hD1,cubicSymbol_one_lower]
  · obtain ⟨u,k,a,ha,he⟩ := unit_ramified_primary_decomposition hc0
    have hu : cubicSymbol D (u:Eisenstein) = 1 := by
      rw [cubicSymbol_unit_periodic hD primary_one u.isUnit h9,cubicSymbol_one_lower]
    have hl : cubicSymbol D lambdaE = 1 := by
      rw [cubicSymbol_lambda_periodic hD primary_one h9,cubicSymbol_one_lower]
    have hca : a ∣ c := by
      refine ⟨(u:Eisenstein)*lambdaE^k,?_⟩
      rw [he]
      ring
    have haD := dvd_trans hca hc
    have hs : cubicSymbol D a = 1 := by
      rw [cubic_reciprocity hD ha,cubicSymbol_congr (residue_eq_of_dvd_sub haD),
        cubic_reciprocity ha primary_one,cubicSymbol_one_lower]
    rw [he,cubicSymbol_mul_upper hD,cubicSymbol_mul_upper hD,cubicSymbol_pow_upper hD,
      hu,hl,hs,one_pow,mul_one,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaKubotaAlternative
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The alternative (b/d) expression for the actual cubic Kubota
multiplier on the principal congruence group. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPrincipalGroup_offDiagonal (g : cubicThetaPrincipalGroup) :
    (3:Eisenstein) ∣ g.val 0 1 ∧ (3:Eisenstein) ∣ g.val 1 0 := by
  have hm : Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (modulus (3:Eisenstein))) g.val = 1 :=
    g.property
  constructor
  · have he := congrArg (fun h : SL(2,Residues (3:Eisenstein)) => h 0 1) hm
    change Ideal.Quotient.mk (modulus (3:Eisenstein)) (g.val 0 1) = 0 at he
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he)
  · have he := congrArg (fun h : SL(2,Residues (3:Eisenstein)) => h 1 0) hm
    change Ideal.Quotient.mk (modulus (3:Eisenstein)) (g.val 1 0) = 0 at he
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he)

lemma cubicThetaPrincipalGroup_det (g : cubicThetaPrincipalGroup) :
    g.val 0 0*g.val 1 1-g.val 0 1*g.val 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using g.val.property

lemma cubicThetaKubota_column_switch (g : cubicThetaPrincipalGroup) :
    cubicSymbol (g.val 0 0) (g.val 1 0) = cubicSymbol (g.val 1 1) (g.val 0 1) := by
  obtain ⟨ha,hd⟩ := cubicThetaPrincipalGroup_diagonal_primary g
  have hdet := cubicThetaPrincipalGroup_det g
  have hdiv : g.val 1 0 ∣ g.val 0 0*g.val 1 1-1 := by
    refine ⟨g.val 0 1,?_⟩
    linear_combination hdet
  have h9 : (9:Eisenstein) ∣ g.val 0 0*g.val 1 1-1 := by
    obtain ⟨x,hx⟩ := (cubicThetaPrincipalGroup_offDiagonal g).1
    obtain ⟨y,hy⟩ := (cubicThetaPrincipalGroup_offDiagonal g).2
    refine ⟨x*y,?_⟩
    calc
      _ = g.val 0 1*g.val 1 0 := by linear_combination hdet
      _ = _ := by rw [hx,hy]; ring
  have hprod := cubicThetaKubota_symbol_one (primary_mul ha hd) h9 hdiv
  rw [cubicSymbol_mul_lower (primary_ne_zero ha) (primary_ne_zero hd)] at hprod
  have hquot : g.val 1 1 ∣ (g.val 0 1*g.val 1 0)-(-1) := by
    refine ⟨g.val 0 0,?_⟩
    linear_combination -hdet
  have hpair : cubicSymbol (g.val 1 1) (g.val 0 1)*cubicSymbol (g.val 1 1) (g.val 1 0) = 1 := by
    rw [←cubicSymbol_mul_upper hd,cubicSymbol_congr (residue_eq_of_dvd_sub hquot),
      cubicSymbol_neg hd,cubic_reciprocity hd primary_one,cubicSymbol_one_lower]
  have hn : cubicSymbol (g.val 1 1) (g.val 1 0) ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hprod
    exact zero_ne_one hprod
  exact mul_right_cancel₀ hn (hprod.trans hpair.symm)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaKubotaProduct
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coprime-column step of the Kubota multiplication law at level nine.
It is proved from cubic reciprocity and the already discharged supplementary
periodicity, not imposed as a new character input. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaKubota_product_coprime
    {a b c d e f : Eisenstein} (ha : primary a) (he : primary e)
    (hdet : a*d-b*c = 1) (hbf : (9:Eisenstein) ∣ b*f)
    (haf : IsCoprime a f) :
    cubicSymbol (a*e+b*f) (c*e+d*f) = cubicSymbol a c*cubicSymbol e f := by
  let A := a*e+b*f
  let C := c*e+d*f
  have hA : primary A := by
    have hb3 : (3:Eisenstein) ∣ b*f := dvd_trans
      (show (3:Eisenstein) ∣ 9 from ⟨3,by norm_num⟩) hbf
    have ht := dvd_add (primary_mul ha he) hb3
    change (3:Eisenstein) ∣ A-1
    rw [show A-1 = a*e-1+b*f by dsimp [A]; ring]
    exact ht
  have hA9 : (9:Eisenstein) ∣ A-a*e := by simpa only [A,add_sub_cancel_left] using hbf
  have hAf : f ∣ A-a*e := by
    simpa only [A,add_sub_cancel_left] using dvd_mul_left f b
  have hsymbol : cubicSymbol A f = cubicSymbol a f*cubicSymbol e f := by
    rw [cubicSymbol_periodic_of_nine_and_numerator hA (primary_mul ha he) hA9 hAf,
      cubicSymbol_mul_lower (primary_ne_zero ha) (primary_ne_zero he)]
  have hac : A ∣ a*C-f := by
    refine ⟨c,?_⟩
    dsimp [A,C]
    linear_combination f*hdet
  have haa : a ∣ A-b*f := by
    refine ⟨e,?_⟩
    dsimp [A]
    ring
  have hm : (cubicSymbol a b*cubicSymbol a f)*cubicSymbol A C =
      cubicSymbol a f*cubicSymbol e f := by
    calc
      _ = cubicSymbol A (a*C) := by
        rw [cubicSymbol_mul_upper hA,cubic_reciprocity hA ha,
          cubicSymbol_congr (residue_eq_of_dvd_sub haa),cubicSymbol_mul_upper ha]
      _ = cubicSymbol A f := cubicSymbol_congr (residue_eq_of_dvd_sub hac)
      _ = _ := hsymbol
  have hacb : a ∣ c*b-(-1) := by
    refine ⟨d,?_⟩
    linear_combination -hdet
  have hcb : cubicSymbol a c*cubicSymbol a b = 1 := by
    rw [←cubicSymbol_mul_upper ha,cubicSymbol_congr (residue_eq_of_dvd_sub hacb),
      cubicSymbol_neg ha,cubic_reciprocity ha primary_one,cubicSymbol_one_lower]
  have hX : cubicSymbol a f ≠ 0 := by
    intro hz
    have h := norm_cubicSymbol_of_isCoprime ha haf
    rw [hz,norm_zero] at h
    norm_num at h
  change cubicSymbol A C = _
  apply mul_left_cancel₀ hX
  linear_combination (cubicSymbol a c)*hm -
    (cubicSymbol a f*cubicSymbol A C)*hcb

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoprimeShear
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit finite-prime avoidance step for the level-nine Kubota
multiplication proof. No prime-distribution theorem is required. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open UniqueFactorizationMonoid
namespace CubicFirstMoment

/-- Choose the shear by multiplying exactly the prime factors of f which
do not divide a. This preserves all good residues and repairs the others. -/
theorem cubicTheta_exists_coprime_shear {a c f : Eisenstein}
    (hf : f ≠ 0) (hac : IsCoprime a (9*c)) :
    ∃ t : Eisenstein, (9:Eisenstein) ∣ t ∧ IsCoprime (a+t*c) f := by
  let m := ((normalizedFactors f).filter (fun p => ¬p ∣ a)).prod
  refine ⟨9*m,⟨m,rfl⟩,?_⟩
  apply IsCoprime.symm
  apply isCoprime_of_prime_dvd (fun h => hf h.1)
  intro p hp hpf hpsum
  by_cases hpa : p ∣ a
  · have hnot : ¬p ∣ 9*c := by
      intro hd
      exact hp.not_isUnit (hac.isRelPrime hpa hd)
    have hnm : ¬p ∣ m := by
      intro hpm
      obtain ⟨q,hq,hpq⟩ := hp.exists_mem_multiset_dvd hpm
      obtain ⟨hqf,hqa⟩ := Multiset.mem_filter.mp hq
      have hqprime := prime_of_normalized_factor q hqf
      have hassoc := hp.irreducible.associated_of_dvd hqprime.irreducible hpq
      exact hqa (dvd_trans hassoc.symm.dvd hpa)
    have hd : p ∣ (9*c)*m := by
      have h := dvd_sub hpsum hpa
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      simp only [add_sub_cancel_left, mul_assoc, mul_comm]
    rcases hp.dvd_mul.mp hd with h | h
    · exact hnot h
    · exact hnm h
  · obtain ⟨q,hqf,hassoc⟩ := exists_mem_normalizedFactors_of_dvd hf hp.irreducible hpf
    have hqa : ¬q ∣ a := by
      intro hqa
      exact hpa (dvd_trans hassoc.dvd hqa)
    have hqm : q ∣ m := Multiset.dvd_prod (Multiset.mem_filter.mpr ⟨hqf,hqa⟩)
    have hpm : p ∣ m := dvd_trans hassoc.dvd hqm
    have hpadd : p ∣ (9*m)*c := dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpm 9) c
    have h := dvd_sub hpsum hpadd
    apply hpa
    simpa only [add_sub_cancel_right] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaKubotaMultiplication
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unrestricted arithmetic multiplication identity for the cubic
Kubota value at level nine. The finite shear removes the auxiliary
coprimality hypothesis from the direct reciprocity calculation. -/
noncomputable section
namespace CubicFirstMoment

lemma primary_add_nine_mul {a t c : Eisenstein} (ha : primary a)
    (ht : (9:Eisenstein) ∣ t) : primary (a+t*c) := by
  obtain ⟨u,hu⟩ := ha
  obtain ⟨v,hv⟩ := ht
  refine ⟨u+3*v*c,?_⟩
  rw [hv]
  linear_combination hu

lemma cubicThetaKubota_shear {a t c : Eisenstein} (ha : primary a)
    (ht : (9:Eisenstein) ∣ t) :
    cubicSymbol (a+t*c) c = cubicSymbol a c := by
  by_cases hc : c = 0
  · simp only [hc,mul_zero,add_zero]
  apply cubicSupplementaryPeriodicity_proved c hc _ _
    (primary_add_nine_mul ha ht) ha
  obtain ⟨u,hu⟩ := ht
  refine ⟨u,?_⟩
  rw [hu]
  ring

lemma cubicThetaKubota_product_nonzero
    {a b c d e f : Eisenstein} (ha : primary a) (he : primary e)
    (hdet : a*d-b*c = 1) (hbf : (9:Eisenstein) ∣ b*f) (hf : f ≠ 0) :
    cubicSymbol (a*e+b*f) (c*e+d*f) = cubicSymbol a c*cubicSymbol e f := by
  have hac : IsCoprime a c := ⟨d,-b,by linear_combination hdet⟩
  have ha9 : IsCoprime a 9 := by
    convert (primary_coprime_three ha).pow_right (n := 2) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  obtain ⟨t,ht,hatf⟩ := cubicTheta_exists_coprime_shear hf (ha9.mul_right hac)
  have hbt : (9:Eisenstein) ∣ (b+t*d)*f := by
    rw [add_mul]
    exact dvd_add hbf (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ht d) f)
  have hdet' : (a+t*c)*d-(b+t*d)*c = 1 := by linear_combination hdet
  have h := cubicThetaKubota_product_coprime (primary_add_nine_mul ha ht) he
    hdet' hbt hatf
  have hA : primary (a*e+b*f) := by
    simpa only [mul_one] using primary_add_nine_mul (c := 1) (primary_mul ha he) hbf
  rw [show (a+t*c)*e+(b+t*d)*f = (a*e+b*f)+t*(c*e+d*f) by ring,
    cubicThetaKubota_shear hA ht,cubicThetaKubota_shear ha ht] at h
  exact h

/-- Arithmetic multiplication, including the zero lower-left entry. -/
theorem cubicThetaKubota_product
    {a b c d e f : Eisenstein} (ha : primary a) (he : primary e)
    (hdet : a*d-b*c = 1) (hbf : (9:Eisenstein) ∣ b*f) (hef : IsCoprime e f) :
    cubicSymbol (a*e+b*f) (c*e+d*f) = cubicSymbol a c*cubicSymbol e f := by
  by_cases hf : f = 0
  · have he1 : e = 1 := primary_unit_eq_one
      (isCoprime_zero_right.mp (hf ▸ hef)) he
    simp only [hf,he1,mul_zero,mul_one,add_zero,cubicSymbol_one_lower]
  · exact cubicThetaKubota_product_nonzero ha he hdet hbf hf

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaKubotaCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic Kubota character on the actual principal congruence group
Gamma_1(3) of DR v3 (5.4). Multiplicativity is derived from reciprocity,
including the noncoprime and zero-entry cases. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaKubotaValue_eq_symbol (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaValue g = cubicSymbol (g.val 0 0) (g.val 1 0) := by
  unfold cubicThetaKubotaValue
  split_ifs with hc
  · have hu := cubicThetaPrincipalGroup_column_coprime g
    rw [hc] at hu
    have ha := primary_unit_eq_one (isCoprime_zero_right.mp hu)
      (cubicThetaPrincipalGroup_diagonal_primary g).1
    rw [ha,cubicSymbol_one_lower]
  · rfl

theorem cubicThetaKubotaValue_mul (g h : cubicThetaPrincipalGroup) :
    cubicThetaKubotaValue (g*h) = cubicThetaKubotaValue g*cubicThetaKubotaValue h := by
  have h9 : (9:Eisenstein) ∣ g.val 0 1*h.val 1 0 := by
    obtain ⟨x,hx⟩ := (cubicThetaPrincipalGroup_offDiagonal g).1
    obtain ⟨y,hy⟩ := (cubicThetaPrincipalGroup_offDiagonal h).2
    exact ⟨x*y,by rw [hx,hy]; ring⟩
  rw [cubicThetaKubotaValue_eq_symbol,cubicThetaKubotaValue_eq_symbol,
    cubicThetaKubotaValue_eq_symbol]
  have hp := cubicThetaKubota_product (cubicThetaPrincipalGroup_diagonal_primary g).1
    (cubicThetaPrincipalGroup_diagonal_primary h).1 (cubicThetaPrincipalGroup_det g)
    h9 (cubicThetaPrincipalGroup_column_coprime h)
  simpa only [Subgroup.coe_mul,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two] using hp

/-- The published multiplier is a genuine multiplicative character. -/
def cubicThetaKubotaCharacter : cubicThetaPrincipalGroup →* ℂ where
  toFun := cubicThetaKubotaValue
  map_one' := by simp [cubicThetaKubotaValue]
  map_mul' := cubicThetaKubotaValue_mul

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBottomRow
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual primitive bottom rows for the cubic Eisenstein series.
Every admissible row is completed inside the principal level-three group,
using Bezout with 3c rather than an unproved choice of congruences. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrincipalGroup_mem_iff (g : SL(2,Eisenstein)) :
    g ∈ cubicThetaPrincipalGroup ↔
      primary (g 0 0) ∧ (3:Eisenstein) ∣ g 0 1 ∧
      (3:Eisenstein) ∣ g 1 0 ∧ primary (g 1 1) := by
  constructor
  · intro hg
    have hdiag := cubicThetaPrincipalGroup_diagonal_primary ⟨g,hg⟩
    have hoff := cubicThetaPrincipalGroup_offDiagonal ⟨g,hg⟩
    exact ⟨hdiag.1,hoff.1,hoff.2,hdiag.2⟩
  · rintro ⟨ha,hb,hc,hd⟩
    let q := Ideal.Quotient.mk (modulus (3:Eisenstein))
    have hz {z : Eisenstein} (h : (3:Eisenstein) ∣ z) : q z = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.mem_span_singleton.mpr h
    have hqa : q (g 0 0) = 1 := by
      have he := hz ha
      rw [map_sub,map_one] at he
      exact sub_eq_zero.mp he
    have hqd : q (g 1 1) = 1 := by
      have he := hz hd
      rw [map_sub,map_one] at he
      exact sub_eq_zero.mp he
    change Matrix.SpecialLinearGroup.map q g = 1
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact hqa
    · exact hz hb
    · exact hz hc
    · exact hqd

@[ext] structure CubicThetaBottomRow where
  c : Eisenstein
  d : Eisenstein
  c_three : (3:Eisenstein) ∣ c
  d_primary : primary d
  coprime : IsCoprime c d

def cubicThetaBottomRow (g : cubicThetaPrincipalGroup) : CubicThetaBottomRow where
  c := g.val 1 0
  d := g.val 1 1
  c_three := (cubicThetaPrincipalGroup_offDiagonal g).2
  d_primary := (cubicThetaPrincipalGroup_diagonal_primary g).2
  coprime := by
    refine ⟨-g.val 0 1,g.val 0 0,?_⟩
    linear_combination cubicThetaPrincipalGroup_det g

theorem cubicThetaBottomRow_surjective : Function.Surjective cubicThetaBottomRow := by
  intro r
  obtain ⟨a,k,h⟩ := (primary_coprime_three r.d_primary).mul_right r.coprime.symm
  have ha : primary a := by
    obtain ⟨t,ht⟩ := r.d_primary
    refine ⟨-a*t-k*r.c,?_⟩
    linear_combination h-a*ht
  let g : SL(2,Eisenstein) := ⟨!![a,-3*k;r.c,r.d],by
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩
  have hg : g ∈ cubicThetaPrincipalGroup := by
    apply (cubicThetaPrincipalGroup_mem_iff g).mpr
    change primary a ∧ (3:Eisenstein) ∣ -3*k ∧ (3:Eisenstein) ∣ r.c ∧ primary r.d
    exact ⟨ha,⟨-k,by ring⟩,r.c_three,r.d_primary⟩
  refine ⟨⟨g,hg⟩,?_⟩
  ext <;> rfl

/-- A completion of the bottom row, with its existence proved above. -/
def CubicThetaBottomRow.completion (r : CubicThetaBottomRow) : cubicThetaPrincipalGroup :=
  Classical.choose (cubicThetaBottomRow_surjective r)

@[simp] lemma CubicThetaBottomRow.completion_row (r : CubicThetaBottomRow) :
    cubicThetaBottomRow r.completion = r :=
  Classical.choose_spec (cubicThetaBottomRow_surjective r)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBottomRowAction
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choice-independent bottom-row multipliers and the exact right action
used to reindex the cubic Eisenstein series. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def CubicThetaBottomRow.phase (r : CubicThetaBottomRow) : ℂ := star (cubicSymbol r.d r.c)

lemma cubicThetaKubotaValue_bottomRow (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaValue g = (cubicThetaBottomRow g).phase := by
  rw [cubicThetaKubotaValue_eq_symbol,cubicThetaKubota_column_switch]
  have hd := (cubicThetaPrincipalGroup_diagonal_primary g).2
  have hr := (cubicThetaBottomRow g).coprime.symm
  change IsCoprime (g.val 1 1) (g.val 1 0) at hr
  have he : g.val 1 1 ∣ g.val 0 1*g.val 1 0-(-1) := by
    refine ⟨g.val 0 0,?_⟩
    linear_combination -cubicThetaPrincipalGroup_det g
  have hprod : cubicSymbol (g.val 1 1) (g.val 0 1)*cubicSymbol (g.val 1 1) (g.val 1 0) = 1 := by
    rw [←cubicSymbol_mul_upper hd,cubicSymbol_congr (residue_eq_of_dvd_sub he),
      cubicSymbol_neg hd,cubic_reciprocity hd primary_one,cubicSymbol_one_lower]
  have hn : cubicSymbol (g.val 1 1) (g.val 1 0)*star (cubicSymbol (g.val 1 1) (g.val 1 0)) = 1 := by
    calc
      _ = (‖cubicSymbol (g.val 1 1) (g.val 1 0)‖:ℂ)^2 := Complex.mul_conj' _
      _ = 1 := by rw [norm_cubicSymbol_of_isCoprime hd hr]; norm_num
  change cubicSymbol (g.val 1 1) (g.val 0 1) = star (cubicSymbol (g.val 1 1) (g.val 1 0))
  calc
    _ = cubicSymbol (g.val 1 1) (g.val 0 1)*
        (cubicSymbol (g.val 1 1) (g.val 1 0)*star (cubicSymbol (g.val 1 1) (g.val 1 0))) := by
      rw [hn,mul_one]
    _ = _ := by rw [←mul_assoc,hprod,one_mul]

lemma CubicThetaBottomRow.phase_norm (r : CubicThetaBottomRow) : ‖r.phase‖ = 1 := by
  exact (norm_star _).trans (norm_cubicSymbol_of_isCoprime r.d_primary r.coprime.symm)

def CubicThetaBottomRow.rightMul (r : CubicThetaBottomRow) (g : cubicThetaPrincipalGroup) :
    CubicThetaBottomRow := cubicThetaBottomRow (r.completion*g)

lemma CubicThetaBottomRow.rightMul_c (r : CubicThetaBottomRow) (g : cubicThetaPrincipalGroup) :
    (r.rightMul g).c = r.c*g.val 0 0+r.d*g.val 1 0 := by
  have hc := congrArg CubicThetaBottomRow.c r.completion_row
  have hd := congrArg CubicThetaBottomRow.d r.completion_row
  change (r.completion.val*g.val) 1 0 = _
  simpa only [cubicThetaBottomRow,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two] using
    congrArg₂ (fun c d => c*g.val 0 0+d*g.val 1 0) hc hd

lemma CubicThetaBottomRow.rightMul_d (r : CubicThetaBottomRow) (g : cubicThetaPrincipalGroup) :
    (r.rightMul g).d = r.c*g.val 0 1+r.d*g.val 1 1 := by
  have hc := congrArg CubicThetaBottomRow.c r.completion_row
  have hd := congrArg CubicThetaBottomRow.d r.completion_row
  change (r.completion.val*g.val) 1 1 = _
  simpa only [cubicThetaBottomRow,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two] using
    congrArg₂ (fun c d => c*g.val 0 1+d*g.val 1 1) hc hd

lemma cubicThetaBottomRow_mul (g h : cubicThetaPrincipalGroup) :
    (cubicThetaBottomRow g).rightMul h = cubicThetaBottomRow (g*h) := by
  apply CubicThetaBottomRow.ext
  · rw [CubicThetaBottomRow.rightMul_c]
    change g.val 1 0*h.val 0 0+g.val 1 1*h.val 1 0 = (g.val*h.val) 1 0
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  · rw [CubicThetaBottomRow.rightMul_d]
    change g.val 1 0*h.val 0 1+g.val 1 1*h.val 1 1 = (g.val*h.val) 1 1
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]

@[simp] lemma CubicThetaBottomRow.rightMul_one (r : CubicThetaBottomRow) : r.rightMul 1 = r := by
  change cubicThetaBottomRow (r.completion*1) = r
  rw [mul_one,r.completion_row]

lemma CubicThetaBottomRow.rightMul_mul (r : CubicThetaBottomRow) (g h : cubicThetaPrincipalGroup) :
    (r.rightMul g).rightMul h = r.rightMul (g*h) := by
  change (cubicThetaBottomRow (r.completion*g)).rightMul h = cubicThetaBottomRow (r.completion*(g*h))
  rw [cubicThetaBottomRow_mul,mul_assoc]

def CubicThetaBottomRow.rightMulEquiv (g : cubicThetaPrincipalGroup) :
    CubicThetaBottomRow ≃ CubicThetaBottomRow where
  toFun r := r.rightMul g
  invFun r := r.rightMul g⁻¹
  left_inv r := by
    change (r.rightMul g).rightMul g⁻¹ = r
    rw [rightMul_mul,mul_inv_cancel,rightMul_one]
  right_inv r := by
    change (r.rightMul g⁻¹).rightMul g = r
    rw [rightMul_mul,inv_mul_cancel,rightMul_one]

lemma CubicThetaBottomRow.phase_rightMul (r : CubicThetaBottomRow) (g : cubicThetaPrincipalGroup) :
    (r.rightMul g).phase = r.phase*cubicThetaKubotaValue g := by
  rw [rightMul,←cubicThetaKubotaValue_bottomRow,cubicThetaKubotaValue_mul,
    cubicThetaKubotaValue_bottomRow,r.completion_row]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisenstein
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic Eisenstein series on the principal group, before analytic
continuation. The bottom-row reindexing proves its actual automorphy;
no transformation formula for the theta coefficients is assumed. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrincipalComplex : cubicThetaPrincipalGroup →* SL(2,ℂ) :=
  (Matrix.SpecialLinearGroup.map (eisensteinRing.subtype : Eisenstein →+* ℂ)).comp
    cubicThetaPrincipalGroup.subtype

@[simp] lemma cubicThetaPrincipalComplex_apply (g : cubicThetaPrincipalGroup) (i j : Fin 2) :
    cubicThetaPrincipalComplex g i j = ((g.val i j:Eisenstein):ℂ) := rfl

def CubicThetaBottomRow.height (r : CubicThetaBottomRow) (p : ℂ × ℝ) : ℝ :=
  p.2/(Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2)

lemma cubicThetaBottomRow_height (g : cubicThetaPrincipalGroup) (p : ℂ × ℝ) :
    (cubicThetaBottomRow g).height p = (cubicThetaMobius (cubicThetaPrincipalComplex g) p).2 := rfl

lemma CubicThetaBottomRow.height_pos (r : CubicThetaBottomRow) {p : ℂ × ℝ} (hp : 0 < p.2) :
    0 < r.height p := by
  rw [←r.completion_row,cubicThetaBottomRow_height]
  exact cubicThetaMobius_height_pos _ hp

lemma CubicThetaBottomRow.height_rightMul (r : CubicThetaBottomRow) (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0 < p.2) :
    (r.rightMul g).height p = r.height (cubicThetaMobius (cubicThetaPrincipalComplex g) p) := by
  change (cubicThetaBottomRow (r.completion*g)).height p = _
  rw [cubicThetaBottomRow_height,map_mul]
  rw [←cubicThetaMobius_comp _ _ hp]
  rw [←cubicThetaBottomRow_height,r.completion_row]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive quadratic majorant for the initial cubic Eisenstein series.
This supplies actual convergence, rather than relying on formal reindexing. -/
noncomputable section
namespace CubicFirstMoment

lemma CubicThetaBottomRow.norm_le_denominator (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0 < p.2) :
    1+norm r.c+norm r.d ≤ cubicThetaHeightConstant p*
      (Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2) := by
  let D := Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2
  have hv := sq_pos_of_pos hp
  have hD : 0 ≤ D := add_nonneg (Complex.normSq_nonneg _)
    (mul_nonneg (norm_nonneg _) (sq_nonneg _))
  have hc : norm r.c ≤ D/p.2^2 := by
    apply (le_div_iff₀ hv).mpr
    dsimp [D]
    linarith [Complex.normSq_nonneg ((r.c:ℂ)*p.1+r.d)]
  have hd : norm r.d ≤ 2*Complex.normSq ((r.c:ℂ)*p.1+r.d)+
      2*norm r.c*Complex.normSq p.1 := by
    have h := normSq_sub_le ((r.c:ℂ)*p.1+r.d) ((r.c:ℂ)*p.1)
    rw [add_sub_cancel_left,Complex.normSq_mul] at h
    simpa only [norm,mul_assoc] using h
  have hn : norm r.c+norm r.d ≤ (2+(1+2*Complex.normSq p.1)/p.2^2)*D := by
    calc
      _ ≤ 2*Complex.normSq ((r.c:ℂ)*p.1+r.d)+(1+2*Complex.normSq p.1)*norm r.c := by linarith
      _ ≤ 2*D+(1+2*Complex.normSq p.1)*(D/p.2^2) := by
        apply add_le_add
        · dsimp [D]
          have h := mul_nonneg (norm_nonneg r.c) (sq_nonneg p.2)
          linarith
        · exact mul_le_mul_of_nonneg_left hc (by linarith [Complex.normSq_nonneg p.1])
      _ = _ := by ring
  have hd1 := one_le_norm (primary_ne_zero r.d_primary)
  change 1+norm r.c+norm r.d ≤ 2*(2+(1+2*Complex.normSq p.1)/p.2^2)*D
  nlinarith [norm_nonneg r.c]

lemma CubicThetaBottomRow.height_le (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0 < p.2) :
    r.height p ≤ (p.2*cubicThetaHeightConstant p)/(1+norm r.c+norm r.d) := by
  have hN : 0 < 1+norm r.c+norm r.d := by linarith [norm_nonneg r.c,norm_nonneg r.d]
  have hD : 0 < Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2 := by
    have h := r.height_pos hp
    exact (div_pos_iff.mp h).resolve_right (fun hh => (not_lt_of_ge hp.le) hh.1) |>.2
  apply (div_le_div_iff₀ hD hN).mpr
  have h := mul_le_mul_of_nonneg_left (r.norm_le_denominator hp) hp.le
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinCusp
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cusp stabilizer and the distinguished zero lower-left
row of the cubic Eisenstein series. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaZeroRow : CubicThetaBottomRow where
  c := 0
  d := 1
  c_three := dvd_zero _
  d_primary := primary_one
  coprime := ⟨0,1,by ring⟩

lemma CubicThetaBottomRow.c_zero_iff (r : CubicThetaBottomRow) :
    r.c = 0 ↔ r = cubicThetaZeroRow := by
  constructor
  · intro hc
    have hunit : IsUnit r.d := isCoprime_zero_left.mp (hc ▸ r.coprime)
    apply CubicThetaBottomRow.ext hc
    exact primary_unit_eq_one hunit r.d_primary
  · rintro rfl
    rfl

def cubicThetaPrincipalTranslation (m : Eisenstein) : cubicThetaPrincipalGroup :=
  let g : SL(2,Eisenstein) := ⟨!![1,3*m;0,1],by simp [Matrix.det_fin_two]⟩
  ⟨g,(cubicThetaPrincipalGroup_mem_iff g).mpr
    ⟨primary_one,⟨m,rfl⟩,dvd_zero _,primary_one⟩⟩

@[simp] lemma cubicThetaPrincipalTranslation_value (m : Eisenstein) :
    cubicThetaKubotaValue (cubicThetaPrincipalTranslation m) = 1 := by
  simp [cubicThetaKubotaValue,cubicThetaPrincipalTranslation]

lemma cubicThetaPrincipalTranslation_complex (m : Eisenstein) :
    cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation m) =
      cubicThetaTranslationMatrix ((3*m:Eisenstein):ℂ) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullRows
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitive rows of the full Eisenstein modular group. Their proper
height function gives the full-group reduction needed for a finite cusp
cover of the principal level-three quotient. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

@[ext] structure CubicThetaPrimitiveRow where
  c : Eisenstein
  d : Eisenstein
  coprime : IsCoprime c d

def cubicThetaFullComplex : SL(2,Eisenstein) →* SL(2,ℂ) :=
  Matrix.SpecialLinearGroup.map (eisensteinRing.subtype : Eisenstein →+* ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProperAction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Eisenstein and principal-group actions are properly
discontinuous. This supplies the topological quotient needed for global
cusp gluing from proved compact-chart transport bounds. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

instance cubicThetaFullPointAction : MulAction SL(2,Eisenstein) CubicThetaPoint :=
  MulAction.compHom CubicThetaPoint cubicThetaFullComplex

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspSeparation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arithmetic separation of the high cusp. Two points above height one
can be equivalent under the principal group only by the actual period
lattice 3 times the Eisenstein integers. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaMobius_height_product_le (g : SL(2,Eisenstein))
    (hc : g 1 0≠0) {p : ℂ × ℝ} (hp : 0<p.2) :
    (cubicThetaMobius (cubicThetaFullComplex g) p).2*p.2≤1 := by
  have hD := cubicThetaMobius_denominator_pos (cubicThetaFullComplex g) hp
  have hN := one_le_norm hc
  have hbound : p.2^2 ≤ cubicThetaMobiusDenominator (cubicThetaFullComplex g) p := by
    change p.2^2≤Complex.normSq (((g 1 0:Eisenstein):ℂ)*p.1+((g 1 1:Eisenstein):ℂ))+
      norm (g 1 0)*p.2^2
    nlinarith [Complex.normSq_nonneg (((g 1 0:Eisenstein):ℂ)*p.1+((g 1 1:Eisenstein):ℂ)),
      mul_le_mul_of_nonneg_right hN (sq_nonneg p.2)]
  change p.2/cubicThetaMobiusDenominator (cubicThetaFullComplex g) p*p.2≤1
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hD).mpr
  nlinarith

lemma cubicThetaMobius_high_overlap (g : SL(2,Eisenstein)) {p : ℂ × ℝ}
    (hp : 1<p.2) (hq : 1<(cubicThetaMobius (cubicThetaFullComplex g) p).2) : g 1 0=0 := by
  by_contra hc
  have h := cubicThetaMobius_height_product_le g hc (lt_trans zero_lt_one hp)
  have hp0 := lt_trans zero_lt_one hp
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFreeAction
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The level-three quotient is a genuine covering: the actual principal
congruence action has no nontrivial point stabilizers. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPrincipalComplex_injective : Function.Injective cubicThetaPrincipalComplex := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  apply Subtype.ext
  exact congrArg (fun k : SL(2,ℂ) => k i j) he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinResidues
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite residue weight used to unfold the cubic Eisenstein series.
Its modulus is exactly 3c, with zero extension outside primary coprime rows. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def CubicThetaBottomRow.shift (r : CubicThetaBottomRow) (m : Eisenstein) : CubicThetaBottomRow :=
  r.rightMul (cubicThetaPrincipalTranslation m)

@[simp] lemma CubicThetaBottomRow.shift_c (r : CubicThetaBottomRow) (m : Eisenstein) :
    (r.shift m).c = r.c := by
  rw [shift,rightMul_c]
  change r.c*1+r.d*0 = r.c
  ring

@[simp] lemma CubicThetaBottomRow.shift_d (r : CubicThetaBottomRow) (m : Eisenstein) :
    (r.shift m).d = r.d+3*r.c*m := by
  rw [shift,rightMul_d]
  change r.c*(3*m)+r.d*1 = r.d+3*r.c*m
  ring

@[simp] lemma CubicThetaBottomRow.shift_phase (r : CubicThetaBottomRow) (m : Eisenstein) :
    (r.shift m).phase = r.phase := by
  rw [shift,phase_rightMul,cubicThetaPrincipalTranslation_value,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowGaussBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary bounds and the exact norm of the fixed dual frequency. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaRowFrequency (h : Eisenstein) : ℂ := (h:ℂ)/(3*traceLambda)

def cubicThetaRowHeatScale (h : Eisenstein) : ℝ :=
  4*Real.pi^2*Complex.normSq (cubicThetaRowFrequency h)

lemma cubicThetaRowHeatScale_eq (h : Eisenstein) :
    cubicThetaRowHeatScale h = (4*Real.pi^2/27)*norm h := by
  unfold cubicThetaRowHeatScale cubicThetaRowFrequency
  rw [Complex.normSq_div, map_mul, traceLambda_normSq]
  norm_num
  change 4*Real.pi^2*(norm h/27) = _
  ring

@[simp] lemma cubicThetaRowHeatScale_zero : cubicThetaRowHeatScale 0 = 0 := by
  simp [cubicThetaRowHeatScale_eq, norm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIncomingRows
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The incoming cutoff series uses the actual primitive bottom rows.
Above the arithmetic cusp threshold at most one row contributes. -/
noncomputable section
namespace CubicFirstMoment

lemma CubicThetaBottomRow.high_height_c_zero (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 1<p.2) (hr : 1 < r.height p) : r.c=0 := by
  have h : 1<(cubicThetaMobius (cubicThetaFullComplex r.completion.val) p).2 := by
    change 1<(cubicThetaBottomRow r.completion).height p
    rwa [r.completion_row]
  have hc := cubicThetaMobius_high_overlap r.completion.val hp h
  have he := congrArg CubicThetaBottomRow.c r.completion_row
  change r.completion.val 1 0=r.c at he
  exact he.symm.trans hc

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIncomingSmooth
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint spatial smoothness of the actual incoming arithmetic series.
The compact row bound makes the sum locally finite before differentiation. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma CubicThetaBottomRow.height_contDiffAt (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0<p.2) : ContDiffAt ℝ ∞ r.height p := by
  have he : r.height=(fun q => (cubicThetaMobius (cubicThetaPrincipalComplex r.completion) q).2) := by
    funext q
    rw [← cubicThetaBottomRow_height,r.completion_row]
  rw [he]
  exact contDiffAt_snd.comp p (cubicThetaMobius_contDiffAt _ hp)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAnnularSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed open-annulus transport of a continuous radial profile.
At most one actual primitive row contributes at any point. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma CubicThetaBottomRow.pointHeight_continuous (r : CubicThetaBottomRow) :
    Continuous (fun p : CubicThetaPoint => r.height p.val) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (r.height_contDiffAt p.property).continuousAt.comp continuous_subtype_val.continuousAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteCover
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-cover domains in the fixed arithmetic action.  This is
used to compare the three root levels without postulating equality of
integrals on different covers. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

structure CubicThetaArithmeticCover where
  group : Subgroup cubicThetaPrincipalGroup
  domain : Set CubicThetaPoint
  measurable : MeasurableSet domain
  unique : ∀ x : CubicThetaPoint, ∃! g : group, g • x∈domain

lemma CubicThetaArithmeticCover.fundamental (D : CubicThetaArithmeticCover)
    (μ : Measure CubicThetaPoint) : IsFundamentalDomain D.group D.domain μ :=
  IsFundamentalDomain.mk' D.measurable.nullMeasurableSet D.unique

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact primitive rows at the inverted cusp. This identifies the
actual transformed Eisenstein series before taking its constant term. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

@[ext] structure CubicThetaInvertedRow where
  c : Eisenstein
  d : Eisenstein
  c_primary : primary c
  d_three : (3:Eisenstein) ∣ d
  coprime : IsCoprime c d

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryIndex
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique indexing of the primary theta frequencies by the original
squarefree and cube variables. There is no multiplicity factor. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev CubicThetaPrimaryPair :=
  {cd : Eisenstein × Eisenstein // primary cd.1 ∧ primary cd.2 ∧ Squarefree cd.1}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeIwahori
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite-index subgroup and cubic diagonal character needed
for the unramified local correspondence. All data come from reduction of
the principal arithmetic group; no local representation input is assumed. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeIwahori (p : Eisenstein) : Subgroup cubicThetaPrincipalGroup where
  carrier := {g | p∣g.val 1 0}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change p∣(g.val*h.val) 1 0
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
    exact dvd_add (dvd_mul_of_dvd_left hg _) (dvd_mul_of_dvd_right hh _)
  inv_mem' := by
    intro g hg
    change p∣(g.val⁻¹) 1 0
    simpa [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two] using dvd_neg.mpr hg

def cubicThetaPrimeIwahoriCharacter (p : Eisenstein) (hp : primaryPrime p) :
    cubicThetaPrimeIwahori p →* ℂ where
  toFun g := cubicSymbol p (g.val.val 0 0)
  map_one' := by
    change cubicSymbol p 1=1
    simpa only [pow_zero] using cubicSymbol_pow_upper hp.1 1 0
  map_mul' g h := by
    change cubicSymbol p ((g.val.val*h.val.val) 0 0)=
      cubicSymbol p (g.val.val 0 0)*cubicSymbol p (h.val.val 0 0)
    have he : p∣(g.val.val*h.val.val) 0 0-(g.val.val 0 0)*(h.val.val 0 0) := by
      simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,add_sub_cancel_left]
      exact dvd_mul_of_dvd_right h.property _
    rw [cubicSymbol_congr (residue_eq_of_dvd_sub he),cubicSymbol_mul_upper hp.1]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integral prime correspondence on the actual level-three group.
Conjugation has its exact cubic diagonal twist, including zero lower-left entries. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPrimeIwahori_division {p : Eisenstein} (hp : p≠0)
    (g : cubicThetaPrimeIwahori p) :
    p*(g.val.val 1 0/p)=g.val.val 1 0 :=
  EuclideanDomain.mul_div_cancel' hp g.property

def cubicThetaPrimeConjugatedMatrix {p : Eisenstein} (hp : p≠0)
    (g : cubicThetaPrimeIwahori p) : SL(2,Eisenstein) where
  val := !![g.val.val 0 0,p*g.val.val 0 1;g.val.val 1 0/p,g.val.val 1 1]
  property := by
    simp [Matrix.det_fin_two]
    calc
      _ = g.val.val 0 0*g.val.val 1 1-g.val.val 0 1*g.val.val 1 0 := by
        linear_combination -(g.val.val 0 1)*(cubicThetaPrimeIwahori_division hp g)
      _ = 1 := cubicThetaPrincipalGroup_det g.val

lemma cubicThetaPrimeConjugatedMatrix_mem {p : Eisenstein} (hp : primary p)
    (g : cubicThetaPrimeIwahori p) :
    cubicThetaPrimeConjugatedMatrix (primary_ne_zero hp) g∈cubicThetaPrincipalGroup := by
  have hd := cubicThetaPrincipalGroup_diagonal_primary g.val
  have ho := cubicThetaPrincipalGroup_offDiagonal g.val
  have hc : (3:Eisenstein)∣g.val.val 1 0/p :=
    (primary_coprime_three hp).symm.dvd_of_dvd_mul_left
      (by rw [cubicThetaPrimeIwahori_division (primary_ne_zero hp) g]; exact ho.2)
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary (g.val.val 0 0) ∧ (3:Eisenstein)∣p*g.val.val 0 1 ∧
    (3:Eisenstein)∣g.val.val 1 0/p ∧ primary (g.val.val 1 1)
  exact ⟨hd.1,dvd_mul_of_dvd_right ho.1 p,hc,hd.2⟩

def cubicThetaPrimeConjugate {p : Eisenstein} (hp : primary p)
    (g : cubicThetaPrimeIwahori p) : cubicThetaPrincipalGroup :=
  ⟨cubicThetaPrimeConjugatedMatrix (primary_ne_zero hp) g,
    cubicThetaPrimeConjugatedMatrix_mem hp g⟩

theorem cubicThetaPrimeConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) :
    cubicThetaKubotaValue g.val=cubicThetaPrimeIwahoriCharacter p hp g*
      cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1 g) := by
  have ha := (cubicThetaPrincipalGroup_diagonal_primary g.val).1
  rw [cubicThetaKubotaValue_eq_symbol,cubicThetaKubotaValue_eq_symbol]
  change cubicSymbol (g.val.val 0 0) (g.val.val 1 0)=
    cubicSymbol p (g.val.val 0 0)*cubicSymbol (g.val.val 0 0) (g.val.val 1 0/p)
  conv_lhs => rw [←cubicThetaPrimeIwahori_division hp.2.ne_zero g]
  rw [cubicSymbol_mul_upper ha,cubic_reciprocity ha hp.1]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDilation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unramified arithmetic correspondence acts on the actual
hyperbolic Eisenstein family, with its cubic diagonal twist retained. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeSquareRoot (p : Eisenstein) : ℂ := (p:ℂ)^(1/2:ℂ)

lemma cubicThetaPrimeSquareRoot_ne_zero {p : Eisenstein} (hp : p≠0) :
    cubicThetaPrimeSquareRoot p≠0 := by
  apply Complex.cpow_ne_zero_iff.mpr
  exact Or.inl (fun hz => hp (Subtype.ext hz))

lemma cubicThetaPrimeSquareRoot_sq (p : Eisenstein) :
    (cubicThetaPrimeSquareRoot p)^2=(p:ℂ) := by
  unfold cubicThetaPrimeSquareRoot
  rw [←Complex.cpow_mul_nat]
  norm_num

def cubicThetaPrimeDilation {p : Eisenstein} (hp : p≠0) : SL(2,ℂ) :=
  ⟨!![cubicThetaPrimeSquareRoot p,0;0,(cubicThetaPrimeSquareRoot p)⁻¹],by
    simp [Matrix.det_fin_two,cubicThetaPrimeSquareRoot_ne_zero hp]⟩

theorem cubicThetaPrimeDilation_intertwines {p : Eisenstein} (hp : primary p)
    (g : cubicThetaPrimeIwahori p) :
    cubicThetaPrimeDilation (primary_ne_zero hp)*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp g)*
        cubicThetaPrimeDilation (primary_ne_zero hp) := by
  have hq := cubicThetaPrimeSquareRoot_ne_zero (primary_ne_zero hp)
  have hs := cubicThetaPrimeSquareRoot_sq p
  have hc : (p:ℂ)*(g.val.val 1 0/p:Eisenstein)=g.val.val 1 0 := by
    exact_mod_cast cubicThetaPrimeIwahori_division (primary_ne_zero hp) g
  apply Subtype.ext
  change ((cubicThetaPrimeDilation (primary_ne_zero hp):Matrix (Fin 2) (Fin 2) ℂ)*
    (cubicThetaPrincipalComplex g.val:Matrix (Fin 2) (Fin 2) ℂ))=
    ((cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp g):Matrix (Fin 2) (Fin 2) ℂ)*
      (cubicThetaPrimeDilation (primary_ne_zero hp):Matrix (Fin 2) (Fin 2) ℂ))
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simp [cubicThetaPrimeDilation,Matrix.mul_apply,Fin.sum_univ_two,
      cubicThetaPrimeConjugate,cubicThetaPrimeConjugatedMatrix,mul_comm]
  · simp only [Matrix.mul_apply,Fin.sum_univ_two,
      cubicThetaPrimeDilation,cubicThetaPrincipalComplex_apply,cubicThetaPrimeConjugate,
      cubicThetaPrimeConjugatedMatrix]
    simp
    field_simp
    linear_combination (g.val.val 0 1:ℂ)*hs
  · simp only [Matrix.mul_apply,Fin.sum_univ_two,
      cubicThetaPrimeDilation,cubicThetaPrincipalComplex_apply,cubicThetaPrimeConjugate,
      cubicThetaPrimeConjugatedMatrix]
    simp
    field_simp
    linear_combination -(g.val.val 1 0/p:Eisenstein)*hs-hc
  · simp [cubicThetaPrimeDilation,Matrix.mul_apply,Fin.sum_univ_two,
      cubicThetaPrimeConjugate,cubicThetaPrimeConjugatedMatrix,mul_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At the cubed prime scale the diagonal cubic twist cancels.
This is the actual integral correspondence needed for the cubed Hecke action. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCube_primary {p : Eisenstein} (hp : primaryPrime p) : primary (p^3) := by
  simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using primary_mul hp.1 (primary_mul hp.1 hp.1)

lemma cubicThetaPrimeCubeIwahori_coprime {p : Eisenstein}
    (g : cubicThetaPrimeIwahori (p^3)) : IsCoprime (g.val.val 0 0) p :=
  (cubicThetaPrincipalGroup_column_coprime g.val).of_isCoprime_of_dvd_right
    (dvd_trans (dvd_pow_self p (by norm_num : (3:ℕ)≠0)) g.property)

theorem cubicThetaPrimeCubeConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^3)) :
    cubicThetaKubotaValue g.val=
      cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g) := by
  have ha := (cubicThetaPrincipalGroup_diagonal_primary g.val).1
  rw [cubicThetaKubotaValue_eq_symbol,cubicThetaKubotaValue_eq_symbol]
  change cubicSymbol (g.val.val 0 0) (g.val.val 1 0)=
    cubicSymbol (g.val.val 0 0) (g.val.val 1 0/p^3)
  conv_lhs => rw [←cubicThetaPrimeIwahori_division (pow_ne_zero 3 hp.2.ne_zero) g]
  rw [cubicSymbol_mul_upper ha,cubicSymbol_pow_upper ha,
    cubicSymbol_cube_of_isCoprime ha p (cubicThetaPrimeCubeIwahori_coprime g),one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootSubgroup
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite-index arithmetic subgroup on which the fractional upper-root
translations can act. The diagonal congruence is retained explicitly. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeRootSubgroup (p : Eisenstein) : Subgroup cubicThetaPrincipalGroup where
  carrier := {g | p^2∣g.val 1 0 ∧ p∣g.val 0 0-g.val 1 1}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    refine ⟨(cubicThetaPrimeIwahori (p^2)).mul_mem hg.1 hh.1,?_⟩
    have hgc : p∣g.val 1 0 := (dvd_pow_self p (by decide : 2≠0)).trans hg.1
    have hhc : p∣h.val 1 0 := (dvd_pow_self p (by decide : 2≠0)).trans hh.1
    change p∣(g.val*h.val) 0 0-(g.val*h.val) 1 1
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
    rw [show (g.val 0 0*h.val 0 0+g.val 0 1*h.val 1 0)-
        (g.val 1 0*h.val 0 1+g.val 1 1*h.val 1 1)=
        g.val 0 0*(h.val 0 0-h.val 1 1)+h.val 1 1*(g.val 0 0-g.val 1 1)+
          g.val 0 1*h.val 1 0-g.val 1 0*h.val 0 1 by ring]
    exact dvd_sub (dvd_add (dvd_add (dvd_mul_of_dvd_right hh.2 _)
      (dvd_mul_of_dvd_right hg.2 _)) (dvd_mul_of_dvd_right hhc _)) (dvd_mul_of_dvd_left hgc _)
  inv_mem' := by
    intro g hg
    refine ⟨(cubicThetaPrimeIwahori (p^2)).inv_mem hg.1,?_⟩
    change p∣(g.val⁻¹) 0 0-(g.val⁻¹) 1 1
    simpa [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,neg_sub] using dvd_neg.mpr hg.2


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootMatrix
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact arithmetic subgroup for translations by 3x/p^3.
It is needed to compare the cubic Hecke correlation with finite Fourier classes. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

abbrev cubicThetaPrimeCubeRootSubgroup (p : Eisenstein) := cubicThetaPrimeRootSubgroup (p^3)

lemma cubicThetaPrimeCubeRoot_lower_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    (p^3)^2*(g.val.val 1 0/(p^3)^2)=g.val.val 1 0 :=
  EuclideanDomain.mul_div_cancel' (pow_ne_zero 2 (pow_ne_zero 3 hp.2.ne_zero)) g.property.1

lemma cubicThetaPrimeCubeRoot_diagonal_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    p^3*((g.val.val 1 1-g.val.val 0 0)/p^3)=g.val.val 1 1-g.val.val 0 0 :=
  EuclideanDomain.mul_div_cancel' (pow_ne_zero 3 hp.2.ne_zero)
    (by simpa only [neg_sub] using dvd_neg.mpr g.property.2)

def cubicThetaPrimeCubeRootMatrix {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) : SL(2,Eisenstein) := by
  let C := g.val.val 1 0/(p^3)^2
  let D := (g.val.val 1 1-g.val.val 0 0)/p^3
  refine ⟨!![g.val.val 0 0+3*x*p^3*C,g.val.val 0 1+3*x*D-9*x^2*C;
    g.val.val 1 0,g.val.val 1 1-3*x*p^3*C],?_⟩
  rw [Matrix.det_fin_two_of]
  have hC : (p^3)^2*C=g.val.val 1 0 := cubicThetaPrimeCubeRoot_lower_division hp g
  have hD : g.val.val 1 1=g.val.val 0 0+p^3*D := by
    have he := cubicThetaPrimeCubeRoot_diagonal_division hp g
    dsimp only [D]
    linear_combination -he
  calc
    _ = g.val.val 0 0*g.val.val 1 1-g.val.val 0 1*g.val.val 1 0 := by
      rw [hD,←hC]
      ring
    _ = 1 := cubicThetaPrincipalGroup_det g.val

lemma cubicThetaPrimeCubeRootMatrix_mem {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaPrimeCubeRootMatrix hp x g∈cubicThetaPrincipalGroup := by
  have ha := (cubicThetaPrincipalGroup_diagonal_primary g.val).1
  have hd := (cubicThetaPrincipalGroup_diagonal_primary g.val).2
  have hb := (cubicThetaPrincipalGroup_offDiagonal g.val).1
  have hc := (cubicThetaPrincipalGroup_offDiagonal g.val).2
  let C := g.val.val 1 0/(p^3)^2
  let D := (g.val.val 1 1-g.val.val 0 0)/p^3
  have ht : (3:Eisenstein)∣3*x*p^3*C := ⟨x*p^3*C,by ring⟩
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary (g.val.val 0 0+3*x*p^3*C) ∧
    (3:Eisenstein)∣g.val.val 0 1+3*x*D-9*x^2*C ∧
    (3:Eisenstein)∣g.val.val 1 0 ∧ primary (g.val.val 1 1-3*x*p^3*C)
  refine ⟨?_,?_,hc,?_⟩
  · change (3:Eisenstein)∣(g.val.val 0 0+3*x*p^3*C)-1
    convert dvd_add ha ht using 1 <;> first | rfl | ring
  · exact dvd_sub (dvd_add hb ⟨x*D,by ring⟩) ⟨3*x^2*C,by ring⟩
  · change (3:Eisenstein)∣(g.val.val 1 1-3*x*p^3*C)-1
    convert dvd_sub hd ht using 1 <;> first | rfl | ring

def cubicThetaPrimeCubeRootConjugate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) : cubicThetaPrimeCubeRootSubgroup p :=
  ⟨⟨cubicThetaPrimeCubeRootMatrix hp x g,cubicThetaPrimeCubeRootMatrix_mem hp x g⟩,by
    refine ⟨g.property.1,?_⟩
    change p^3∣(g.val.val 0 0+3*x*p^3*(g.val.val 1 0/(p^3)^2))-
      (g.val.val 1 1-3*x*p^3*(g.val.val 1 0/(p^3)^2))
    convert dvd_add g.property.2 (show p^3∣6*x*p^3*(g.val.val 1 0/(p^3)^2) from
      ⟨6*x*(g.val.val 1 0/(p^3)^2),by ring⟩) using 1; ring⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootMatrix
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral formulas for conjugation by the fractional upper root 3x/p.
The defining congruences give actual integral quotients. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeRoot_lower_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) :
    p^2*(g.val.val 1 0/p^2)=g.val.val 1 0 :=
  EuclideanDomain.mul_div_cancel' (pow_ne_zero 2 hp.2.ne_zero) g.property.1

lemma cubicThetaPrimeRoot_diagonal_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) :
    p*((g.val.val 1 1-g.val.val 0 0)/p)=g.val.val 1 1-g.val.val 0 0 :=
  EuclideanDomain.mul_div_cancel' hp.2.ne_zero (by simpa only [neg_sub] using dvd_neg.mpr g.property.2)

def cubicThetaPrimeRootMatrix {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) : SL(2,Eisenstein) := by
  let C := g.val.val 1 0/p^2
  let D := (g.val.val 1 1-g.val.val 0 0)/p
  refine ⟨!![g.val.val 0 0+3*x*p*C,g.val.val 0 1+3*x*D-9*x^2*C;
    g.val.val 1 0,g.val.val 1 1-3*x*p*C],?_⟩
  rw [Matrix.det_fin_two_of]
  have hC : p^2*C=g.val.val 1 0 := cubicThetaPrimeRoot_lower_division hp g
  have hD : g.val.val 1 1=g.val.val 0 0+p*D := by
    have he := cubicThetaPrimeRoot_diagonal_division hp g
    dsimp only [D]
    linear_combination -he
  calc
    _ = g.val.val 0 0*g.val.val 1 1-g.val.val 0 1*g.val.val 1 0 := by
      rw [hD,←hC]
      ring
    _ = 1 := cubicThetaPrincipalGroup_det g.val

lemma cubicThetaPrimeRootMatrix_mem {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaPrimeRootMatrix hp x g∈cubicThetaPrincipalGroup := by
  have ha := (cubicThetaPrincipalGroup_diagonal_primary g.val).1
  have hd := (cubicThetaPrincipalGroup_diagonal_primary g.val).2
  have hb := (cubicThetaPrincipalGroup_offDiagonal g.val).1
  have hc := (cubicThetaPrincipalGroup_offDiagonal g.val).2
  let C := g.val.val 1 0/p^2
  let D := (g.val.val 1 1-g.val.val 0 0)/p
  have ht : (3:Eisenstein)∣3*x*p*C := ⟨x*p*C,by ring⟩
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary (g.val.val 0 0+3*x*p*C) ∧
    (3:Eisenstein)∣g.val.val 0 1+3*x*D-9*x^2*C ∧
    (3:Eisenstein)∣g.val.val 1 0 ∧ primary (g.val.val 1 1-3*x*p*C)
  refine ⟨?_,?_,hc,?_⟩
  · change (3:Eisenstein)∣(g.val.val 0 0+3*x*p*C)-1
    convert dvd_add ha ht using 1 <;> first | rfl | ring
  · exact dvd_sub (dvd_add hb ⟨x*D,by ring⟩) ⟨3*x^2*C,by ring⟩
  · change (3:Eisenstein)∣(g.val.val 1 1-3*x*p*C)-1
    convert dvd_sub hd ht using 1 <;> first | rfl | ring

def cubicThetaPrimeRootConjugate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) : cubicThetaPrimeRootSubgroup p :=
  ⟨⟨cubicThetaPrimeRootMatrix hp x g,cubicThetaPrimeRootMatrix_mem hp x g⟩,by
    refine ⟨g.property.1,?_⟩
    change p∣(g.val.val 0 0+3*x*p*(g.val.val 1 0/p^2))-
      (g.val.val 1 1-3*x*p*(g.val.val 1 0/p^2))
    convert dvd_add g.property.2 (show p∣6*x*p*(g.val.val 1 0/p^2) from
      ⟨6*x*(g.val.val 1 0/p^2),by ring⟩) using 1; ring⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integral root matrix is conjugation by an actual upper translation
after the prime dilation. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimeRootIwahori {p : Eisenstein} (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaPrimeIwahori p :=
  ⟨g.val,(dvd_pow_self p (by decide : 2≠0)).trans g.property.1⟩

lemma cubicThetaPrimeRoot_lower_single_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) :
    g.val.val 1 0/p=p*(g.val.val 1 0/p^2) := by
  apply mul_left_cancel₀ hp.2.ne_zero
  have hh : p*(g.val.val 1 0/p)=g.val.val 1 0 :=
    EuclideanDomain.mul_div_cancel' hp.2.ne_zero
      ((dvd_pow_self p (by decide : 2≠0)).trans g.property.1)
  rw [hh]
  have he := cubicThetaPrimeRoot_lower_division hp g
  linear_combination -he

theorem cubicThetaPrimeRootConjugate_dilation {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeRootIwahori (cubicThetaPrimeRootConjugate hp x g))=
      cubicThetaPrincipalTranslation x*cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeRootIwahori g)*
        (cubicThetaPrincipalTranslation x)⁻¹ := by
  let a := g.val.val 0 0
  let b := g.val.val 0 1
  let c := g.val.val 1 0
  let d := g.val.val 1 1
  let C := c/p^2
  let B := (d-a)/p
  have hc : c/p=p*C := cubicThetaPrimeRoot_lower_single_division hp g
  have hd : p*B=d-a := cubicThetaPrimeRoot_diagonal_division hp g
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  dsimp only [cubicThetaPrimeConjugate,cubicThetaPrimeConjugatedMatrix,
    cubicThetaPrimeRootIwahori,cubicThetaPrimeRootConjugate,cubicThetaPrimeRootMatrix,
    cubicThetaPrincipalTranslation]
  simp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,neg_zero]
  change (!![a+3*x*p*C,p*(b+3*x*B-9*x^2*C);c/p,d-3*x*p*C] :
    Matrix (Fin 2) (Fin 2) Eisenstein)=
    !![1,3*x;0,1]*!![a,p*b;c/p,d]*!![1,-(3*x);0,1]
  rw [hc]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring_nf
  linear_combination (3*x:Eisenstein)*hd

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fractional root conjugation preserves the actual cubic Kubota
multiplier on its arithmetic subgroup. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrincipalTranslation_inverse_value (x : Eisenstein) :
    cubicThetaKubotaValue (cubicThetaPrincipalTranslation x)⁻¹=1 := by
  have he := cubicThetaKubotaCharacter.map_mul (cubicThetaPrincipalTranslation x)
    (cubicThetaPrincipalTranslation x)⁻¹
  rw [mul_inv_cancel,map_one] at he
  change 1=cubicThetaKubotaValue (cubicThetaPrincipalTranslation x)*
    cubicThetaKubotaValue (cubicThetaPrincipalTranslation x)⁻¹ at he
  rw [cubicThetaPrincipalTranslation_value,one_mul] at he
  exact he.symm

lemma cubicThetaPrimeRootConjugate_diagonal_character {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) :
    cubicSymbol p ((cubicThetaPrimeRootConjugate hp x g).val.val 0 0)=
      cubicSymbol p (g.val.val 0 0) := by
  apply cubicSymbol_congr
  apply residue_eq_of_dvd_sub
  refine ⟨3*x*(g.val.val 1 0/p^2),?_⟩
  change (g.val.val 0 0+3*x*p*(g.val.val 1 0/p^2))-g.val.val 0 0=_
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral conjugation at the cubic root scale. The cubic twist of
the dilation is trivial, so the original multiplier is retained exactly. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimeCubeRootIwahori {p : Eisenstein} (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaPrimeIwahori (p^3) :=
  ⟨g.val,(dvd_pow_self (p^3) (by decide : 2≠0)).trans g.property.1⟩

lemma cubicThetaPrimeCubeRoot_lower_single_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    g.val.val 1 0/p^3=p^3*(g.val.val 1 0/(p^3)^2) := by
  apply mul_left_cancel₀ (pow_ne_zero 3 hp.2.ne_zero)
  have hh : p^3*(g.val.val 1 0/p^3)=g.val.val 1 0 :=
    EuclideanDomain.mul_div_cancel' (pow_ne_zero 3 hp.2.ne_zero)
      ((dvd_pow_self (p^3) (by decide : 2≠0)).trans g.property.1)
  rw [hh]
  have he := cubicThetaPrimeCubeRoot_lower_division hp g
  linear_combination -he

theorem cubicThetaPrimeCubeRootConjugate_dilation {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp)
      (cubicThetaPrimeCubeRootIwahori (cubicThetaPrimeCubeRootConjugate hp x g))=
      cubicThetaPrincipalTranslation x*cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp)
        (cubicThetaPrimeCubeRootIwahori g)*(cubicThetaPrincipalTranslation x)⁻¹ := by
  let a := g.val.val 0 0
  let b := g.val.val 0 1
  let c := g.val.val 1 0
  let d := g.val.val 1 1
  let C := c/(p^3)^2
  let B := (d-a)/p^3
  have hc : c/p^3=p^3*C := cubicThetaPrimeCubeRoot_lower_single_division hp g
  have hd : p^3*B=d-a := cubicThetaPrimeCubeRoot_diagonal_division hp g
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  dsimp only [cubicThetaPrimeConjugate,cubicThetaPrimeConjugatedMatrix,
    cubicThetaPrimeCubeRootIwahori,cubicThetaPrimeCubeRootConjugate,cubicThetaPrimeCubeRootMatrix,
    cubicThetaPrincipalTranslation]
  simp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,neg_zero]
  change (!![a+3*x*p^3*C,p^3*(b+3*x*B-9*x^2*C);c/p^3,d-3*x*p^3*C] :
    Matrix (Fin 2) (Fin 2) Eisenstein)=
    !![1,3*x;0,1]*!![a,p^3*b;c/p^3,d]*!![1,-(3*x);0,1]
  rw [hc]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring_nf
  linear_combination (3*x:Eisenstein)*hd

theorem cubicThetaPrimeCubeRootConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaKubotaValue (cubicThetaPrimeCubeRootConjugate hp x g).val=
      cubicThetaKubotaValue g.val := by
  have hM : cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp)
      (cubicThetaPrimeCubeRootIwahori (cubicThetaPrimeCubeRootConjugate hp x g)))=
      cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp)
        (cubicThetaPrimeCubeRootIwahori g)) := by
    rw [cubicThetaPrimeCubeRootConjugate_dilation,cubicThetaKubotaValue_mul,
      cubicThetaKubotaValue_mul,cubicThetaPrincipalTranslation_value,
      cubicThetaPrincipalTranslation_inverse_value,one_mul,mul_one]
  exact (cubicThetaPrimeCubeConjugate_kubota hp
    (cubicThetaPrimeCubeRootIwahori (cubicThetaPrimeCubeRootConjugate hp x g))).trans
      (hM.trans (cubicThetaPrimeCubeConjugate_kubota hp (cubicThetaPrimeCubeRootIwahori g)).symm)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootAction
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal cubic-scale fractional root preserves the arithmetic
subgroup and its actual cubic multiplier. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeCubeRootElement {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : SL(2,ℂ) :=
  (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹*
    cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)*
      cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)

theorem cubicThetaPrimeCubeRootElement_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaPrimeCubeRootElement hp x*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootConjugate hp x g).val*
        cubicThetaPrimeCubeRootElement hp x := by
  let D := cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)
  let t := cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)
  let q := cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp)
    (cubicThetaPrimeCubeRootIwahori g))
  let q' := cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp)
    (cubicThetaPrimeCubeRootIwahori (cubicThetaPrimeCubeRootConjugate hp x g)))
  have hg : D*cubicThetaPrincipalComplex g.val=q*D :=
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeCube_primary hp) (cubicThetaPrimeCubeRootIwahori g)
  have hg' : D*cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootConjugate hp x g).val=q'*D :=
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeCube_primary hp)
      (cubicThetaPrimeCubeRootIwahori (cubicThetaPrimeCubeRootConjugate hp x g))
  have hq : q'=t*q*t⁻¹ := by
    change cubicThetaPrincipalComplex _=_
    rw [cubicThetaPrimeCubeRootConjugate_dilation,map_mul,map_mul,map_inv]
  have ht : t*q=q'*t := by rw [hq]; group
  have hg'' : D⁻¹*q'*D=cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootConjugate hp x g).val := by
    rw [mul_assoc,←hg']
    group
  change D⁻¹*t*D*cubicThetaPrincipalComplex g.val=
    cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootConjugate hp x g).val*(D⁻¹*t*D)
  calc
    _ = D⁻¹*t*(D*cubicThetaPrincipalComplex g.val) := by group
    _ = D⁻¹*t*(q*D) := by rw [hg]
    _ = D⁻¹*(t*q)*D := by group
    _ = D⁻¹*(q'*t)*D := by rw [ht]
    _ = (D⁻¹*q'*D)*(D⁻¹*t*D) := by group
    _ = _ := by rw [hg'']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootTranslation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic-scale fractional root has its literal translation parameter. Its additive
law and integral periods will be used to average over the cube modulus. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRootElement_translation {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeCubeRootElement hp x=
      cubicThetaTranslationMatrix (((3*x:Eisenstein):ℂ)/((p^3:Eisenstein):ℂ)) := by
  let D := cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)
  let t := cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)
  let u := cubicThetaTranslationMatrix (((3*x:Eisenstein):ℂ)/((p^3:Eisenstein):ℂ))
  have hD : D*u=t*D := by
    rw [show t=cubicThetaTranslationMatrix ((3*x:Eisenstein):ℂ) from
      cubicThetaPrincipalTranslation_complex x]
    apply Subtype.ext
    change (D:Matrix (Fin 2) (Fin 2) ℂ)*(u:Matrix (Fin 2) (Fin 2) ℂ)=
      (cubicThetaTranslationMatrix ((3*x:Eisenstein):ℂ):Matrix (Fin 2) (Fin 2) ℂ)*
        (D:Matrix (Fin 2) (Fin 2) ℂ)
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [D,u,cubicThetaPrimeDilation,cubicThetaTranslationMatrix,
        Matrix.mul_apply,Fin.sum_univ_two]
    have hs : (p:ℂ)^3=(cubicThetaPrimeSquareRoot (p^3))^2 := by
      have hc : ((p^3:Eisenstein):ℂ)=(p:ℂ)^3 := map_pow eisensteinRing.val p 3
      exact hc.symm.trans (cubicThetaPrimeSquareRoot_sq (p^3)).symm
    rw [hs]
    field_simp [cubicThetaPrimeSquareRoot_ne_zero (pow_ne_zero 3 hp.2.ne_zero)]
  change D⁻¹*t*D=u
  calc
    _ = D⁻¹*(t*D) := by group
    _ = D⁻¹*(D*u) := by rw [hD]
    _ = u := by group

@[simp] lemma cubicThetaPrimeCubeRootElement_zero {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootElement hp 0=1 := by
  rw [cubicThetaPrimeCubeRootElement_translation]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubicThetaTranslationMatrix]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootAutomorphism
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fractional roots normalize the actual arithmetic subgroup. The
inverse is the negative root, with no choice of an abstract local model. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootConjugate_complex {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootConjugate hp x g).val=
      cubicThetaPrimeCubeRootElement hp x*cubicThetaPrincipalComplex g.val*
        (cubicThetaPrimeCubeRootElement hp x)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  exact (cubicThetaPrimeCubeRootElement_intertwines hp x g).symm

@[simp] lemma cubicThetaPrimeCubeRootConjugate_zero {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) : cubicThetaPrimeCubeRootConjugate hp 0 g=g := by
  apply Subtype.ext
  apply cubicThetaPrincipalComplex_injective
  simp only [cubicThetaPrimeCubeRootConjugate_complex,cubicThetaPrimeCubeRootElement_zero,
    one_mul,inv_one,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootAction
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual complex root element acts on the arithmetic subgroup with
its original cubic multiplier. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeRootElement {p : Eisenstein} (hp : primaryPrime p) (x : Eisenstein) : SL(2,ℂ) :=
  (cubicThetaPrimeDilation hp.2.ne_zero)⁻¹*cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)*
    cubicThetaPrimeDilation hp.2.ne_zero

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootTranslation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fractional root has its literal translation parameter. Its additive
law and integral periods will be used to average over the prime residue field. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaPrimeRootElement_translation {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeRootElement hp x=
      cubicThetaTranslationMatrix (((3*x:Eisenstein):ℂ)/(p:ℂ)) := by
  let D := cubicThetaPrimeDilation hp.2.ne_zero
  let t := cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)
  let u := cubicThetaTranslationMatrix (((3*x:Eisenstein):ℂ)/(p:ℂ))
  have hD : D*u=t*D := by
    rw [show t=cubicThetaTranslationMatrix ((3*x:Eisenstein):ℂ) from
      cubicThetaPrincipalTranslation_complex x]
    apply Subtype.ext
    change (D:Matrix (Fin 2) (Fin 2) ℂ)*(u:Matrix (Fin 2) (Fin 2) ℂ)=
      (cubicThetaTranslationMatrix ((3*x:Eisenstein):ℂ):Matrix (Fin 2) (Fin 2) ℂ)*
        (D:Matrix (Fin 2) (Fin 2) ℂ)
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [D,u,cubicThetaPrimeDilation,cubicThetaTranslationMatrix,
        Matrix.mul_apply,Fin.sum_univ_two]
    rw [←cubicThetaPrimeSquareRoot_sq p]
    field_simp [cubicThetaPrimeSquareRoot_ne_zero hp.2.ne_zero]
  change D⁻¹*t*D=u
  calc
    _ = D⁻¹*(t*D) := by group
    _ = D⁻¹*(D*u) := by rw [hD]
    _ = u := by group

@[simp] lemma cubicThetaPrimeRootElement_zero {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeRootElement hp 0=1 := by
  rw [cubicThetaPrimeRootElement_translation]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubicThetaTranslationMatrix]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootOperators
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual linear root translations on the finite-cover section space.
Integral translations act trivially, so the operators depend only on the
residue class of their parameter modulo the prime. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeRootIntegralTranslation (p x : Eisenstein) :
    cubicThetaPrimeRootSubgroup p :=
  ⟨cubicThetaPrincipalTranslation x,by
    constructor <;> simp [cubicThetaPrincipalTranslation]⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inversion of the cubic completion kernel. The Euler variable
for a prime ideal is first weighted, then replaced by its cube. Thus the
series identities below retain the actual cube-divisor support; they are
not ordinary (uncubed) convolution identities. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev ComplexIdealSeries := MvPowerSeries EisensteinIdealPrime ℂ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal level/angular Voronoi input of Dunn--Radziwill,
arXiv:2109.07463v3, Proposition 5.3, equations (5.79)--(5.82), pp.33--34.
The raw formula is kept separate from its proved Gauss/phase normalization.
The index `n` below denotes the actual frequency `n / lambda`; zero is excluded.
No estimate for a completed sum is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev MetaplecticDualArgument := {n : Eisenstein // n ≠ 0}

@[simp] lemma complexAngular_coe (ℓ : ℤ) (a : Eisenstein) :
    complexAngular ℓ a = theta ℓ a := rfl

end CubicFirstMoment

end

end OAI
end



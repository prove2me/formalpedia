-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplittingIdeals
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SplittingIdeals
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:55:53.633979+00:00
-- url     : https://prove2.me/theorems/b7f548eb-3d10-45f6-b3ee-05bf5fae8ed0
-- title:
--   Splitting Ideals
-- statement:
--   Definitions and structural lemmas for Splitting Ideals, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SplittingIdeals.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Galois
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitIntegralClosure
import Mathlib.NumberTheory.RamificationInertia.Galois
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_exists_splitUpperIdeal_auxiliary_residue_root
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ArtinSchreier_ker_card
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepTranslation_apply_auxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluate_constants
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluate_eq_zero_iff
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
theorem exists_splitBaseUpperIdeal
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    ∃ R : Ideal (SplitIntegralClosure Q P x hx),
      R.IsMaximal ∧
        R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing) := by
  letI : IsDiscreteValuationRing Q.place.valuationRing :=
    Q.place.valuationRing_isDiscreteValuationRing
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := SplitIntegralClosure Q P x hx)
    (IsLocalRing.maximalIdeal Q.place.valuationRing)
noncomputable def splitBaseUpperIdeal
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    Ideal (SplitIntegralClosure Q P x hx) :=
  Classical.choose (exists_splitBaseUpperIdeal Q P x hx)
theorem splitBaseUpperIdeal_isMaximal
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    (splitBaseUpperIdeal Q P x hx).IsMaximal :=
  (Classical.choose_spec (exists_splitBaseUpperIdeal Q P x hx)).1
theorem splitBaseUpperIdeal_liesOver
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    (splitBaseUpperIdeal Q P x hx).LiesOver
      (IsLocalRing.maximalIdeal Q.place.valuationRing) :=
  (Classical.choose_spec (exists_splitBaseUpperIdeal Q P x hx)).2
noncomputable def splitBaseUpperPrime
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
      (SplitIntegralClosure Q P x hx) := by
  letI : (splitBaseUpperIdeal Q P x hx).IsPrime :=
    (splitBaseUpperIdeal_isMaximal Q P x hx).isPrime
  letI : (splitBaseUpperIdeal Q P x hx).LiesOver
      (IsLocalRing.maximalIdeal Q.place.valuationRing) :=
    splitBaseUpperIdeal_liesOver Q P x hx
  exact Ideal.primesOver.mk _ (splitBaseUpperIdeal Q P x hx)
noncomputable def splitUpperPrime
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
      (SplitIntegralClosure Q P x hx) :=
  (stepTranslation P x hx c) • splitBaseUpperPrime Q P x hx
theorem galRestrict_stepTranslation_apply_auxiliaryCoordinate
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    galRestrict Q.place.valuationRing K (StepField P x hx)
        (SplitIntegralClosure Q P x hx) (stepTranslation P x hx c)
        (splitIntegralAuxiliaryCoordinate Q P x hx hregular) =
      splitIntegralAuxiliaryCoordinate Q P x hx hregular +
        algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
          (GlobalPlace.constantsToValuationRing Q.place (c : F256)) := by
  apply IsIntegralClosure.algebraMap_injective
    (SplitIntegralClosure Q P x hx) Q.place.valuationRing
      (StepField P x hx)
  rw [algebraMap_galRestrict_apply]
  change stepTranslation P x hx c (stepAuxiliaryCoordinate P x hx) =
    stepAuxiliaryCoordinate P x hx +
      algebraMap F256 (StepField P x hx) (c : F256)
  exact stepTranslation_apply_auxiliaryCoordinate P x hx c
theorem translated_auxiliary_residue_mem_splitUpperPrime
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (b : F256)
    (hb : splitIntegralAuxiliaryCoordinate Q P x hx hregular -
        algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
          (GlobalPlace.constantsToValuationRing Q.place b) ∈
        splitBaseUpperIdeal Q P x hx)
    (c : LinearMap.ker f256ArtinSchreier) :
    splitIntegralAuxiliaryCoordinate Q P x hx hregular +
          algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
            (GlobalPlace.constantsToValuationRing Q.place (c : F256)) -
        algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
          (GlobalPlace.constantsToValuationRing Q.place b) ∈
      (splitUpperPrime Q P x hx c).1 := by
  let σ := stepTranslation P x hx c
  let φ := galRestrict Q.place.valuationRing K (StepField P x hx)
    (SplitIntegralClosure Q P x hx) σ
  have hmap := Ideal.mem_map_of_mem φ hb
  change _ ∈ Ideal.map φ (splitBaseUpperIdeal Q P x hx)
  rw [← galRestrict_stepTranslation_apply_auxiliaryCoordinate
    Q P x hx hregular c]
  rw [← φ.commutes]
  rw [← map_sub]
  exact hmap
theorem splitUpperPrime_injective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Function.Injective (splitUpperPrime Q P x hx) := by
  intro c d hcd
  let R := splitBaseUpperIdeal Q P x hx
  letI : R.IsMaximal := splitBaseUpperIdeal_isMaximal Q P x hx
  letI : R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing) :=
    splitBaseUpperIdeal_liesOver Q P x hx
  obtain ⟨b, hb, hroot⟩ :=
    exists_splitUpperIdeal_auxiliary_residue_root
      Q P x hx hregular R
  have hc := translated_auxiliary_residue_mem_splitUpperPrime
    Q P x hx hregular b hroot c
  have hd := translated_auxiliary_residue_mem_splitUpperPrime
    Q P x hx hregular b hroot d
  rw [hcd] at hc
  let I : Ideal (SplitIntegralClosure Q P x hx) :=
    (splitUpperPrime Q P x hx d).1
  have hconstants :
      algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
            (GlobalPlace.constantsToValuationRing Q.place (c : F256)) -
          algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
            (GlobalPlace.constantsToValuationRing Q.place (d : F256)) ∈ I := by
    have hidentity :
        algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
              (GlobalPlace.constantsToValuationRing Q.place (c : F256)) -
            algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
              (GlobalPlace.constantsToValuationRing Q.place (d : F256)) =
          (splitIntegralAuxiliaryCoordinate Q P x hx hregular +
                algebraMap Q.place.valuationRing
                  (SplitIntegralClosure Q P x hx)
                  (GlobalPlace.constantsToValuationRing Q.place (c : F256)) -
              algebraMap Q.place.valuationRing
                (SplitIntegralClosure Q P x hx)
                (GlobalPlace.constantsToValuationRing Q.place b)) -
            (splitIntegralAuxiliaryCoordinate Q P x hx hregular +
                algebraMap Q.place.valuationRing
                  (SplitIntegralClosure Q P x hx)
                  (GlobalPlace.constantsToValuationRing Q.place (d : F256)) -
              algebraMap Q.place.valuationRing
                (SplitIntegralClosure Q P x hx)
                (GlobalPlace.constantsToValuationRing Q.place b)) := by
      ring
    rw [hidentity]
    exact I.sub_mem hc hd
  have hbase :
      GlobalPlace.constantsToValuationRing Q.place (c : F256) -
          GlobalPlace.constantsToValuationRing Q.place (d : F256) ∈
        IsLocalRing.maximalIdeal Q.place.valuationRing := by
    rw [Ideal.over_def I (IsLocalRing.maximalIdeal Q.place.valuationRing)]
    change algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
        (GlobalPlace.constantsToValuationRing Q.place (c : F256) -
          GlobalPlace.constantsToValuationRing Q.place (d : F256)) ∈ I
    simpa only [map_sub] using hconstants
  have heval :
      Q.evaluate
          (GlobalPlace.constantsToValuationRing Q.place (c : F256) -
            GlobalPlace.constantsToValuationRing Q.place (d : F256)) = 0 :=
    (Q.evaluate_eq_zero_iff _).2 hbase
  have hvalue : (c : F256) - (d : F256) = 0 := by
    simpa only [map_sub, Q.evaluate_constants] using heval
  apply Subtype.ext
  exact sub_eq_zero.mp hvalue
theorem split_primesOver_ncard
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    ((IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
      (SplitIntegralClosure Q P x hx)).ncard = 16 := by
  let O := Q.place.valuationRing
  let S := SplitIntegralClosure Q P x hx
  let L := StepField P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let G := L ≃ₐ[K] L
  letI : IsDiscreteValuationRing O :=
    Q.place.valuationRing_isDiscreteValuationRing
  letI : MulSemiringAction G S :=
    IsIntegralClosure.MulSemiringAction O K L S
  letI : IsGaloisGroup G O S :=
    IsGaloisGroup.of_isFractionRing G O S K L
  have hlower : 16 ≤ (m.primesOver S).ncard := by
    calc
      16 = Nat.card (LinearMap.ker f256ArtinSchreier) := by
        rw [Nat.card_eq_fintype_card, f256ArtinSchreier_ker_card]
      _ ≤ Nat.card (m.primesOver S) :=
        Nat.card_le_card_of_injective (splitUpperPrime Q P x hx)
          (splitUpperPrime_injective Q P x hx hregular)
      _ = (m.primesOver S).ncard := Nat.card_coe_set_eq _
  have he : m.ramificationIdxIn S ≠ 0 :=
    Ideal.ramificationIdxIn_ne_zero G
  have hf : m.inertiaDegIn S ≠ 0 :=
    Ideal.inertiaDegIn_ne_zero G
  have hfundamental :
      (m.primesOver S).ncard *
          (m.ramificationIdxIn S * m.inertiaDegIn S) = 16 := by
    calc
      (m.primesOver S).ncard *
            (m.ramificationIdxIn S * m.inertiaDegIn S) = Nat.card G :=
        Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
          m S G
      _ = 16 := stepField_algEquiv_card P x hx
  apply le_antisymm
  · calc
      (m.primesOver S).ncard ≤
          (m.primesOver S).ncard *
            (m.ramificationIdxIn S * m.inertiaDegIn S) :=
        Nat.le_mul_of_pos_right _
          (Nat.mul_pos (Nat.pos_of_ne_zero he) (Nat.pos_of_ne_zero hf))
      _ = 16 := hfundamental
  · exact hlower
noncomputable def splitUpperPrimeEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    LinearMap.ker f256ArtinSchreier ≃
      (IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
        (SplitIntegralClosure Q P x hx) := by
  apply Equiv.ofBijective (splitUpperPrime Q P x hx)
  apply (Nat.bijective_iff_injective_and_card _).2
  refine ⟨splitUpperPrime_injective Q P x hx hregular, ?_⟩
  calc
    Nat.card (LinearMap.ker f256ArtinSchreier) = 16 := by
      rw [Nat.card_eq_fintype_card, f256ArtinSchreier_ker_card]
    _ = ((IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
        (SplitIntegralClosure Q P x hx)).ncard :=
      (split_primesOver_ncard Q P x hx hregular).symm
    _ = Nat.card
        ((IsLocalRing.maximalIdeal Q.place.valuationRing).primesOver
          (SplitIntegralClosure Q P x hx)) :=
      (Nat.card_coe_set_eq _).symm
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth



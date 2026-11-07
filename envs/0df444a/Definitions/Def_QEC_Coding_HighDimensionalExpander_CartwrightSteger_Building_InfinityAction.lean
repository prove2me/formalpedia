-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:57:50.138214+00:00
-- url     : https://prove2.me/theorems/f18884a3-27c3-4d21-80f9-b748daab4391
-- title:
--   Infinity Action
-- statement:
--   Definitions and structural lemmas for Infinity Action, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
noncomputable def constantUnitMatrixHom
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  Units.map (constantMatrixEmbedding P r).toMonoidHom
noncomputable def infinityCyclicCoefficient
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (k : ℕ) :
    (ConstantExtension P r)ˣ :=
  u * ((constantFrobeniusUnitEquiv P r ^ k) u)⁻¹
noncomputable def infinityConjugationCoefficient
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    ConstantExtension P r :=
  ((constantFrobenius P r ^ (k : ℤ)) (u : ConstantExtension P r) /
      (u : ConstantExtension P r)) * ζ -
    ((constantFrobenius P r ^ ((k : ℤ) - 1))
        (u : ConstantExtension P r) /
      (constantFrobenius P r ^ (-1 : ℤ))
        (u : ConstantExtension P r)) *
      (constantFrobenius P r ^ (-1 : ℤ)) ζ
noncomputable def infinityConjugationCoefficientNat
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    ConstantExtension P r :=
  ((constantFrobenius P r ^ k) (u : ConstantExtension P r) /
      (u : ConstantExtension P r)) * ζ -
    ((constantFrobenius P r).symm
          ((constantFrobenius P r ^ k) (u : ConstantExtension P r)) /
        (constantFrobenius P r).symm (u : ConstantExtension P r)) *
      (constantFrobenius P r).symm ζ
noncomputable def infinityConjugationCorrectionSum
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k bound : ℕ) (ζ : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  ∑ i ∈ Finset.range bound,
    constantMatrix P r
        (infinityConjugationCoefficient P r u k ζ *
          (infinityCyclicCoefficient P r u i : ConstantExtension P r)) *
      cyclicGeneratorMatrix P r ^ i
noncomputable def infinityConjugationFormula
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k +
    infinityConjugationCorrectionSum P r u k k ζ +
    (splittingY P r)⁻¹ •
      infinityConjugationCorrectionSum P r u k r.matrixRank ζ
noncomputable def constantConjugatedCartwrightStegerB
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantUnitMatrix P r u * cartwrightStegerB P r *
    (constantUnitMatrix P r u)⁻¹
noncomputable def infinityCyclicInverseCoefficient
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    ConstantExtension P r :=
  (u : ConstantExtension P r) *
    ((constantFrobenius P r).symm (u : ConstantExtension P r))⁻¹
noncomputable def constantConjugatedBInverseExpansion
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  1 + (splittingY P r)⁻¹ •
    ∑ i ∈ Finset.range r.matrixRank,
      constantMatrix P r (infinityCyclicCoefficient P r u i) *
        cyclicGeneratorMatrix P r ^ i
noncomputable def constantConjugatedBInverseTail
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  ∑ i ∈ Finset.range r.matrixRank,
    constantMatrix P r (infinityCyclicCoefficient P r u i) *
      cyclicGeneratorMatrix P r ^ i
noncomputable def infinityLeadingMonomial
    (P : BasePrime) (r : Rank) (k : ℕ) (ζ : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k
noncomputable def infinityDefectMonomial
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantMatrix P r
      (infinityCyclicInverseCoefficient P r u *
        (constantFrobenius P r).symm ζ) *
    cyclicGeneratorInverseMatrix P r * cyclicGeneratorMatrix P r ^ k
noncomputable def infinityLeadingTailTerm
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) (ζ : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantMatrix P r
      (ζ * (constantFrobenius P r ^ k)
        (infinityCyclicCoefficient P r u i : ConstantExtension P r)) *
    cyclicGeneratorMatrix P r ^ (k + i)
noncomputable def infinityDefectTailTerm
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) (ζ : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantMatrix P r
      ((infinityCyclicInverseCoefficient P r u *
          (constantFrobenius P r).symm ζ) *
        (constantFrobenius P r).symm
          ((constantFrobenius P r ^ k)
            (infinityCyclicCoefficient P r u i : ConstantExtension P r))) *
    cyclicGeneratorInverseMatrix P r *
      cyclicGeneratorMatrix P r ^ (k + i)
noncomputable def infinityShiftedCorrectionTerm
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) (ζ : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantMatrix P r
      (infinityConjugationCoefficient P r u k ζ *
        (infinityCyclicCoefficient P r u (k + i) :
          ConstantExtension P r)) *
    cyclicGeneratorMatrix P r ^ (k + i)
noncomputable def infinityCorrectionTerm
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) (ζ : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantMatrix P r
      (infinityConjugationCoefficient P r u k ζ *
        (infinityCyclicCoefficient P r u i : ConstantExtension P r)) *
    cyclicGeneratorMatrix P r ^ i
def HasUpperUnipotentInfinityConjugation
    (P : BasePrime) (r : Rank)
    (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)) : Prop :=
  ∀ (k : Fin r.matrixRank) (ζ : ConstantExtension P r),
    ∃ lower tail : ℕ → ConstantExtension P r,
      ((g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) *
          (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ (k : ℕ))) *
          ((g⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (SplittingFunctionField P r)) =
        constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ (k : ℕ) +
          (∑ i ∈ Finset.range (k : ℕ),
            constantMatrix P r (lower i) * cyclicGeneratorMatrix P r ^ i) +
          (splittingY P r)⁻¹ •
            ∑ i ∈ Finset.range r.matrixRank,
              constantMatrix P r (tail i) * cyclicGeneratorMatrix P r ^ i
end QEC.Coding.HighDimensionalExpander.CartwrightSteger



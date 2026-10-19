-- Prove2me | Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
-- name    : QAlgorithms_Defs_GeneralPOVMs
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:37:19.424149+00:00
-- url     : https://prove2.me/theorems/425fa478-3cb2-44d4-ae93-b43c08881b2d
-- title:
--   GeneralPOVMs
-- statement:
--   GeneralPOVMs
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\GeneralPOVMs.lean

import Definitions.Def_QAlgorithms_Defs_Information
noncomputable section

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace QAlgorithms.Measurements

/-- Normalized operator measure on a finite register and an arbitrary measurable
outcome space (1508.01797 p.6; 1508.01907 p.7; 2305.18519 pp.3-4).
Matrix-valued HasSum is equivalent to entrywise HasSum in finite dimension. -/
structure OperatorPOVM (I O : Type*) [Fintype I] [DecidableEq I] [MeasurableSpace O] where
  operator : Set O → Matrix I I ℂ
  empty : operator ∅ = 0
  total : operator Set.univ = 1
  positive : ∀ B, MeasurableSet B → (operator B).PosSemidef
  additive : ∀ B : ℕ → Set O, (∀ i, MeasurableSet (B i)) →
    Pairwise (fun i j => Disjoint (B i) (B j)) →
    HasSum (fun i => operator (B i)) (operator (⋃ i, B i))

/-- Continuous real Born pairing for scalar outcome measures (1508.01797 p.6). -/
def bornFunctional {I : Type*} [Fintype I] (rho : Matrix I I ℂ) :
    Matrix I I ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun M => effectProb M rho
    map_add' := by intro A B; simp [effectProb, Matrix.add_mul, Matrix.trace_add]
    map_smul' := by intro r A; simp [effectProb, Matrix.smul_mul, Matrix.trace_smul] }

/-- Positive effects have nonnegative Born weights on PSD inputs
(1508.01797 p.6, Born rule). -/
theorem born_nonnegative {I : Type*} [Fintype I] [DecidableEq I]
    {M rho : Matrix I I ℂ} (hM : M.PosSemidef) (hrho : rho.PosSemidef) :
    0 ≤ effectProb M rho := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hrho.nonneg
  have hp := (hM.mul_mul_conjTranspose_same B).trace_nonneg
  rw [effectProb, hB]
  have ht : (M * (star B * B)).trace = (B * M * Bᴴ).trace := by
    simp only [Matrix.star_eq_conjTranspose]
    rw [← Matrix.trace_mul_cycle]
    simp [Matrix.mul_assoc]
  rw [ht]
  exact hp.1

/-- Constructed scalar Born measure, without renormalization
(1508.01797 p.6; 1508.01907 p.7; 2305.18519 p.3). -/
def bornLaw {I O : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace O]
    (E : OperatorPOVM I O) (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) : Measure O :=
  Measure.ofMeasurable (fun B _ => ENNReal.ofReal (effectProb (E.operator B) rho))
    (by simp [E.empty, effectProb]) (by
      intro B hB hd
      have hs := (E.additive B hB hd).map (bornFunctional rho) (bornFunctional rho).continuous
      change HasSum (fun i => effectProb (E.operator (B i)) rho)
        (effectProb (E.operator (⋃ i, B i)) rho) at hs
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun i => born_nonnegative (E.positive _ (hB i)) hrho.1) hs.summable, hs.tsum_eq])

/-- Born probabilities agree with the trace formula on measurable events
(1508.01797 p.6). -/
theorem bornLaw_apply {I O : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace O]
    (E : OperatorPOVM I O) (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (B : Set O) (hB : MeasurableSet B) :
    bornLaw E rho hrho B = ENNReal.ofReal (effectProb (E.operator B) rho) :=
  Measure.ofMeasurable_apply B hB

example {I O : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace O]
    (E : OperatorPOVM I O) (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) :
    bornLaw E rho hrho Set.univ = 1 := by
  rw [bornLaw_apply E rho hrho _ MeasurableSet.univ]
  simp [E.total, effectProb, hrho.2]

example {I O : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace O]
    (E : OperatorPOVM I O) (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) :
    bornLaw E rho hrho ∅ = 0 := measure_empty

end QAlgorithms.Measurements



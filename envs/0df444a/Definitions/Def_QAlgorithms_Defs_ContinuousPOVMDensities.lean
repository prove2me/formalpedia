-- Prove2me | Definitions.Def_QAlgorithms_Defs_ContinuousPOVMDensities
-- name    : QAlgorithms_Defs_ContinuousPOVMDensities
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:38:05.086972+00:00
-- url     : https://prove2.me/theorems/b4da2e1d-d2cf-4127-81e9-1aa9a2aa445a
-- title:
--   ContinuousPOVMDensities
-- statement:
--   ContinuousPOVMDensities
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ContinuousPOVMDensities.lean

import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

open MeasureTheory
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Measurements
/-- Borel matrix densities (1508.01797 p.6; 1508.01907 p.7). -/
local instance matrixMeasurable (I : Type*) [Fintype I] : MeasurableSpace (Matrix I I ℂ) := borel _

/-- An integrable PSD operator density with its specified finite reference measure
(1508.01797 pp.5-6,12; 1508.01907 pp.7-8). -/
structure DensityPOVM (I O : Type*) [Fintype I] [DecidableEq I] [MeasurableSpace O] where
  reference : Measure O
  finite : IsFiniteMeasure reference
  density : O → Matrix I I ℂ
  measurable : Measurable density
  positive : ∀ o, (density o).PosSemidef
  integrable : Integrable density reference
  complete : ∫ o, density o ∂reference = 1

/-- Real-linear continuous conjugate transpose for Hermitian operator integrals
(1508.01797 p.6, integrated POVM). -/
def adjointFunctional {I : Type*} [Fintype I] :
    Matrix I I ℂ →L[ℝ] Matrix I I ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := Matrix.conjTranspose
    map_add' := Matrix.conjTranspose_add
    map_smul' := by intro r A; simp [Matrix.conjTranspose_smul] }

/-- Continuous quadratic form used to derive positivity of integrated effects
(1508.01797 p.6). -/
def quadraticFunctional {I : Type*} [Fintype I] (v : I → ℂ) :
    Matrix I I ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A => star v ⬝ᵥ A.mulVec v
    map_add' := by intro A B; simp [Matrix.add_mulVec, dotProduct_add]
    map_smul' := by intro r A; simp [Matrix.smul_mulVec, dotProduct_smul] }

/-- Integrating PSD matrices preserves positivity; this is legality, not tomography
accuracy (1508.01797 p.6). -/
theorem integral_positive {I O : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace O]
    (mu : Measure O) (D : O → Matrix I I ℂ) (hD : Integrable D mu)
    (hp : ∀ o, (D o).PosSemidef) : (∫ o, D o ∂mu).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (adjointFunctional (I:=I)) (∫ o, D o ∂mu) = ∫ o, D o ∂mu
    rw [← (adjointFunctional (I:=I)).integral_comp_comm hD]
    change (∫ o, (D o)ᴴ ∂mu) = ∫ o, D o ∂mu
    simp only [(hp _).isHermitian.eq]
  · intro v
    change 0 ≤ (quadraticFunctional v) (∫ o, D o ∂mu)
    rw [← (quadraticFunctional v).integral_comp_comm hD]
    exact integral_nonneg (fun o => (hp o).dotProduct_mulVec_nonneg v)

/-- Convert the density to its actual operator measure by restricted integrals
(1508.01797 p.6; 1508.01907 p.7). -/
def densityOperatorPOVM {I O : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace O]
    (D : DensityPOVM I O) : OperatorPOVM I O where
  operator := fun B => ∫ o in B, D.density o ∂D.reference
  empty := by simp
  total := by simpa using D.complete
  positive := fun B _ => integral_positive _ _ D.integrable.integrableOn D.positive
  additive := fun B hm hd => hasSum_integral_iUnion hm hd D.integrable.integrableOn

example {I O : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace O]
    (D : DensityPOVM I O) :
    (densityOperatorPOVM D).operator Set.univ = 1 := (densityOperatorPOVM D).total

example {I O : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace O]
    (D : DensityPOVM I O) :
    (densityOperatorPOVM D).operator ∅ = 0 := by simp [densityOperatorPOVM]

end QAlgorithms.Measurements



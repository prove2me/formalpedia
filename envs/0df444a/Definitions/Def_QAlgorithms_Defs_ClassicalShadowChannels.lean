-- Prove2me | Definitions.Def_QAlgorithms_Defs_ClassicalShadowChannels
-- name    : QAlgorithms_Defs_ClassicalShadowChannels
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:13:50.04846+00:00
-- url     : https://prove2.me/theorems/ec164c0d-7e9b-4757-8751-72359d9fb198
-- title:
--   ClassicalShadowChannels
-- statement:
--   ClassicalShadowChannels
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ClassicalShadowChannels.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
noncomputable section

open MeasureTheory
open scoped Matrix

namespace QAlgorithms.ClassicalShadows

variable {n m d k b w M K N c out : ℕ}
/-- Borel sigma-algebra on the source unitary ensemble (2002.08953 p.11). -/
instance unitaryMeasurableSpace (n : ℕ) : MeasurableSpace (Matrix.unitaryGroup (Qubits n) ℂ) :=
  borel _

/-- The preceding sigma-algebra is Borel (2002.08953 p.11). -/
instance unitaryBorelSpace (n : ℕ) : BorelSpace (Matrix.unitaryGroup (Qubits n) ℂ) := ⟨rfl⟩

/-- Matrix index space used by the unitary measurement primitive
(2002.08953 p.11). -/
abbrev Space (n : ℕ) := Matrix (Qubits n) (Qubits n) ℂ

/-- Complex superoperator coefficients for the averaged measurement channel,
2002.08953 p.11 Eq.(S2). Integrating coefficients before linear extension
ensures complex linearity for all operators, not just density matrices. -/
def channelCoefficient (mu : Measure (Matrix.unitaryGroup (Qubits n) ℂ))
    (hmu : IsProbabilityMeasure mu) (i j k l : Qubits n) : ℂ :=
  ∫ U, ∑ b, star ((U : Space n) b i) * (U : Space n) b j *
    (U : Space n) b k * star ((U : Space n) b l) ∂mu

/-- Constructed averaged channel, 2002.08953 p.11 Eq.(S2). -/
def measurementChannel (mu : Measure (Matrix.unitaryGroup (Qubits n) ℂ))
    (hmu : IsProbabilityMeasure mu) :
    Space n →ₗ[ℂ] Space n where
  toFun X := Matrix.of fun i j => ∑ k, ∑ l, channelCoefficient mu hmu i j k l * X k l
  map_add' X Y := by ext i j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a X := by ext i j; simp [Finset.mul_sum, mul_left_comm]

/-- A fixed Borel probability ensemble with informationally complete
constructed channel (2002.08953 p.11 Definition 1). -/
structure MeasurementPrimitive (n : ℕ) where
  ensemble : Measure (Matrix.unitaryGroup (Qubits n) ℂ)
  probability : IsProbabilityMeasure ensemble
  complete : Function.Injective (measurementChannel ensemble probability)

/-- Inverse of the channel's linear equivalence, constructed solely from
the primitive's completeness (2002.08953 pp.11–12 Eqs.(S3),(S9)). -/
def inverseChannel (P : MeasurementPrimitive n) : Space n ≃ₗ[ℂ] Space n :=
  (LinearEquiv.ofBijective (measurementChannel P.ensemble P.probability)
    ⟨P.complete, LinearMap.injective_iff_surjective.mp P.complete⟩).symm

/-- Classical snapshot, 2002.08953 p.11 Eq.(S3).
Its type permits negative eigenvalues. -/
def snapshot (P : MeasurementPrimitive n) (U : Matrix.unitaryGroup (Qubits n) ℂ)
    (b : Qubits n) : Space n :=
  inverseChannel P (star (U : Space n) * pureDensity (ket b) * (U : Space n))

/-- Sanity check for the modeled source objects (arxiv-2002.08953v2, PDF pp.11,12). -/
example (mu : Measure (Matrix.unitaryGroup (Qubits n) ℂ)) (hmu : IsProbabilityMeasure mu) :
    measurementChannel mu hmu 0 = 0 := map_zero _

/-- Sanity check for the modeled source objects (arxiv-2002.08953v2, PDF pp.11,12). -/
example (P : MeasurementPrimitive n) (X : Space n) :
    inverseChannel P (measurementChannel P.ensemble P.probability X) = X :=
  (LinearEquiv.ofBijective (measurementChannel P.ensemble P.probability)
    ⟨P.complete, LinearMap.injective_iff_surjective.mp P.complete⟩).symm_apply_apply X

end QAlgorithms.ClassicalShadows



-- Prove2me | Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
-- name    : QEC_Distillation_Universality_OneQubitMagicState
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T11:59:01.287278+00:00
-- url     : https://prove2.me/theorems/a9c55756-7253-440f-a2fe-1ba1cbdd28a1
-- title:
--   One Qubit Magic State
-- statement:
--   Definitions and structural lemmas for One Qubit Magic State, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_pauliI_trace
import Theorems.Thm_QEC_Semantics_Qubit_pauliX_adjoint
import Theorems.Thm_QEC_Semantics_Qubit_pauliX_trace
import Theorems.Thm_QEC_Semantics_Qubit_pauliY_adjoint
import Theorems.Thm_QEC_Semantics_Qubit_pauliY_trace
import Theorems.Thm_QEC_Semantics_Qubit_pauliZ_adjoint
import Theorems.Thm_QEC_Semantics_Qubit_pauliZ_trace
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace OneQubitMagic
open Semantics Semantics.Qubit
def tBloch : PauliAxis -> Real
  | .x | .y | .z => (Real.sqrt 3)⁻¹
def hBloch : PauliAxis -> Real
  | .x | .z => (Real.sqrt 2)⁻¹
  | .y => 0
def tReference : TDirection := ⟨fun _ => .pos, by intro i; simp⟩
def hReference : HDirection :=
  ⟨fun | .x => .pos | .y => .zero | .z => .pos, by decide +kernel⟩
def signedCoordinateValue : SignedCoordinate -> Int
  | .neg => -1
  | .zero => 0
  | .pos => 1
def tBlochOfDirection (d : TDirection) : PauliAxis -> Real :=
  fun i => (signedCoordinateValue (d.1 i) : Real) * (Real.sqrt 3)⁻¹
def hBlochOfDirection (d : HDirection) : PauliAxis -> Real :=
  fun i => (signedCoordinateValue (d.1 i) : Real) * (Real.sqrt 2)⁻¹
def blochNormSq (r : PauliAxis -> Real) : Real :=
  r .x ^ 2 + r .y ^ 2 + r .z ^ 2
def pauliOperator : PauliAxis -> Operator QubitSpace
  | .x => pauliX
  | .y => pauliY
  | .z => pauliZ
def blochOperator (r : PauliAxis -> Real) : Operator QubitSpace :=
  (r .x : Complex) • pauliX + (r .y : Complex) • pauliY + (r .z : Complex) • pauliZ
def blochProjector (r : PauliAxis -> Real) : Operator QubitSpace :=
  (2 : Complex)⁻¹ • (1 + blochOperator r)
def tProjector (d : TDirection) : Operator QubitSpace :=
  blochProjector (tBlochOfDirection d)
def hProjector (d : HDirection) : Operator QubitSpace :=
  blochProjector (hBlochOfDirection d)
def hadamardBlochAction (r : PauliAxis -> Real) : PauliAxis -> Real
  | .x => r .z
  | .y => -r .y
  | .z => r .x
def phaseBlochAction (r : PauliAxis -> Real) : PauliAxis -> Real
  | .x => -r .y
  | .y => r .x
  | .z => r .z
def densityBloch (rho : DensityOperator QubitSpace) : PauliAxis → Real :=
  fun i => (LinearMap.trace Complex QubitSpace
    (pauliOperator i * rho.toOperator)).re
theorem blochOperator_apply_zero (r : PauliAxis -> Real) (psi : QubitSpace) :
    blochOperator r psi 0 =
      (r .z : Complex) * psi 0 + ((r .x : Complex) - Complex.I * r .y) * psi 1 := by
  simp [blochOperator]
  ring
theorem blochOperator_apply_one (r : PauliAxis -> Real) (psi : QubitSpace) :
    blochOperator r psi 1 =
      ((r .x : Complex) + Complex.I * r .y) * psi 0 - (r .z : Complex) * psi 1 := by
  simp [blochOperator]
  ring
theorem bloch_square_zero_diagonal (r : PauliAxis -> Real) :
    (r .z : Complex) * (r .z : Complex) +
        ((r .x : Complex) - Complex.I * (r .y : Complex)) *
          ((r .x : Complex) + Complex.I * (r .y : Complex)) =
      (blochNormSq r : Complex) := by
  have hIry_sq :
      (Complex.I * (r .y : Complex)) * (Complex.I * (r .y : Complex)) =
        -((r .y : Complex) * (r .y : Complex)) := by
    calc
      (Complex.I * (r .y : Complex)) * (Complex.I * (r .y : Complex)) =
          (Complex.I * Complex.I) * ((r .y : Complex) * (r .y : Complex)) := by ring
      _ = -((r .y : Complex) * (r .y : Complex)) := by
        rw [Complex.I_mul_I]
        ring
  have hcast : (blochNormSq r : Complex) =
      (r .x : Complex) * (r .x : Complex) +
        (r .y : Complex) * (r .y : Complex) +
        (r .z : Complex) * (r .z : Complex) := by
    simp only [blochNormSq]
    norm_cast
    ring
  rw [hcast]
  rw [show ((r .x : Complex) - Complex.I * (r .y : Complex)) *
      ((r .x : Complex) + Complex.I * (r .y : Complex)) =
      (r .x : Complex) * (r .x : Complex) -
        (Complex.I * (r .y : Complex)) * (Complex.I * (r .y : Complex)) by ring]
  rw [hIry_sq]
  ring
theorem bloch_square_zero_off_diagonal (r : PauliAxis -> Real) :
    (r .z : Complex) * ((r .x : Complex) - Complex.I * (r .y : Complex)) -
      ((r .x : Complex) - Complex.I * (r .y : Complex)) * (r .z : Complex) = 0 := by
  ring
theorem bloch_square_one_diagonal (r : PauliAxis -> Real) :
    (r .z : Complex) * (r .z : Complex) +
        ((r .x : Complex) + Complex.I * (r .y : Complex)) *
          ((r .x : Complex) - Complex.I * (r .y : Complex)) =
      (blochNormSq r : Complex) := by
  have hIry_sq :
      (Complex.I * (r .y : Complex)) * (Complex.I * (r .y : Complex)) =
        -((r .y : Complex) * (r .y : Complex)) := by
    calc
      (Complex.I * (r .y : Complex)) * (Complex.I * (r .y : Complex)) =
          (Complex.I * Complex.I) * ((r .y : Complex) * (r .y : Complex)) := by ring
      _ = -((r .y : Complex) * (r .y : Complex)) := by
        rw [Complex.I_mul_I]
        ring
  have hcast : (blochNormSq r : Complex) =
      (r .x : Complex) * (r .x : Complex) +
        (r .y : Complex) * (r .y : Complex) +
        (r .z : Complex) * (r .z : Complex) := by
    simp only [blochNormSq]
    norm_cast
    ring
  rw [hcast]
  rw [show ((r .x : Complex) + Complex.I * (r .y : Complex)) *
      ((r .x : Complex) - Complex.I * (r .y : Complex)) =
      (r .x : Complex) * (r .x : Complex) -
        (Complex.I * (r .y : Complex)) * (Complex.I * (r .y : Complex)) by ring]
  rw [hIry_sq]
  ring
theorem bloch_square_one_off_diagonal (r : PauliAxis -> Real) :
    ((r .x : Complex) + Complex.I * (r .y : Complex)) * (r .z : Complex) -
      (r .z : Complex) * ((r .x : Complex) + Complex.I * (r .y : Complex)) = 0 := by
  ring
theorem tBloch_normalized : blochNormSq tBloch = 1 := by
  have hsquare : Real.sqrt (3 : Real) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt (3 : Real) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  simp only [blochNormSq, tBloch]
  field_simp [hne]
  nlinarith
theorem hBloch_normalized : blochNormSq hBloch = 1 := by
  have hsquare : Real.sqrt (2 : Real) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt (2 : Real) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  simp only [blochNormSq, hBloch]
  field_simp [hne]
  nlinarith
theorem tDirection_signedCoordinate_sq_sum (d : TDirection) :
    signedCoordinateValue (d.1 .x) ^ 2 + signedCoordinateValue (d.1 .y) ^ 2 +
      signedCoordinateValue (d.1 .z) ^ 2 = 3 := by
  rcases d with ⟨d, hd⟩
  revert d
  decide +kernel
theorem hDirection_signedCoordinate_sq_sum (d : HDirection) :
    signedCoordinateValue (d.1 .x) ^ 2 + signedCoordinateValue (d.1 .y) ^ 2 +
      signedCoordinateValue (d.1 .z) ^ 2 = 2 := by
  rcases d with ⟨d, hd⟩
  revert d
  decide +kernel
theorem tBlochOfDirection_normalized (d : TDirection) :
    blochNormSq (tBlochOfDirection d) = 1 := by
  have hsum :
      (signedCoordinateValue (d.1 .x) : Real) ^ 2 +
          (signedCoordinateValue (d.1 .y) : Real) ^ 2 +
          (signedCoordinateValue (d.1 .z) : Real) ^ 2 = 3 := by
    exact_mod_cast tDirection_signedCoordinate_sq_sum d
  have hsquare : Real.sqrt (3 : Real) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt (3 : Real) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  simp only [blochNormSq, tBlochOfDirection]
  calc
    _ = ((signedCoordinateValue (d.1 .x) : Real) ^ 2 +
          (signedCoordinateValue (d.1 .y) : Real) ^ 2 +
          (signedCoordinateValue (d.1 .z) : Real) ^ 2) *
        (Real.sqrt 3)⁻¹ ^ 2 := by ring
    _ = 3 * (Real.sqrt 3)⁻¹ ^ 2 := by rw [hsum]
    _ = 1 := by
      field_simp [hne]
      exact hsquare.symm
theorem hBlochOfDirection_normalized (d : HDirection) :
    blochNormSq (hBlochOfDirection d) = 1 := by
  have hsum :
      (signedCoordinateValue (d.1 .x) : Real) ^ 2 +
          (signedCoordinateValue (d.1 .y) : Real) ^ 2 +
          (signedCoordinateValue (d.1 .z) : Real) ^ 2 = 2 := by
    exact_mod_cast hDirection_signedCoordinate_sq_sum d
  have hsquare : Real.sqrt (2 : Real) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt (2 : Real) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  simp only [blochNormSq, hBlochOfDirection]
  calc
    _ = ((signedCoordinateValue (d.1 .x) : Real) ^ 2 +
          (signedCoordinateValue (d.1 .y) : Real) ^ 2 +
          (signedCoordinateValue (d.1 .z) : Real) ^ 2) *
        (Real.sqrt 2)⁻¹ ^ 2 := by ring
    _ = 2 * (Real.sqrt 2)⁻¹ ^ 2 := by rw [hsum]
    _ = 1 := by
      field_simp [hne]
      exact hsquare.symm
theorem blochOperator_square (r : PauliAxis -> Real) :
    blochOperator r * blochOperator r = (blochNormSq r : Complex) • 1 := by
  ext psi b
  fin_cases b
  · change (blochOperator r (blochOperator r psi)) 0 =
      (((blochNormSq r : Complex) • (1 : Operator QubitSpace)) psi) 0
    rw [blochOperator_apply_zero r (blochOperator r psi),
      blochOperator_apply_zero r psi,
      blochOperator_apply_one r psi]
    change
      (r .z : Complex) * ((r .z : Complex) * psi 0 +
          ((r .x : Complex) - Complex.I * (r .y : Complex)) * psi 1) +
        ((r .x : Complex) - Complex.I * (r .y : Complex)) *
          (((r .x : Complex) + Complex.I * (r .y : Complex)) * psi 0 -
            (r .z : Complex) * psi 1) =
        (blochNormSq r : Complex) * psi 0
    calc
      _ = ((r .z : Complex) * (r .z : Complex) +
            ((r .x : Complex) - Complex.I * (r .y : Complex)) *
              ((r .x : Complex) + Complex.I * (r .y : Complex))) * psi 0 +
          ((r .z : Complex) * ((r .x : Complex) - Complex.I * (r .y : Complex)) -
            ((r .x : Complex) - Complex.I * (r .y : Complex)) * (r .z : Complex)) * psi 1 := by
        ring
      _ = (blochNormSq r : Complex) * psi 0 + 0 * psi 1 := by
        rw [bloch_square_zero_diagonal, bloch_square_zero_off_diagonal]
      _ = _ := by simp
  · change (blochOperator r (blochOperator r psi)) 1 =
      (((blochNormSq r : Complex) • (1 : Operator QubitSpace)) psi) 1
    rw [blochOperator_apply_one r (blochOperator r psi),
      blochOperator_apply_zero r psi,
      blochOperator_apply_one r psi]
    change
      ((r .x : Complex) + Complex.I * (r .y : Complex)) *
          ((r .z : Complex) * psi 0 +
            ((r .x : Complex) - Complex.I * (r .y : Complex)) * psi 1) -
        (r .z : Complex) *
          (((r .x : Complex) + Complex.I * (r .y : Complex)) * psi 0 -
            (r .z : Complex) * psi 1) =
        (blochNormSq r : Complex) * psi 1
    calc
      _ = (((r .x : Complex) + Complex.I * (r .y : Complex)) * (r .z : Complex) -
            (r .z : Complex) * ((r .x : Complex) + Complex.I * (r .y : Complex))) * psi 0 +
          ((r .z : Complex) * (r .z : Complex) +
            ((r .x : Complex) + Complex.I * (r .y : Complex)) *
              ((r .x : Complex) - Complex.I * (r .y : Complex))) * psi 1 := by
        ring
      _ = 0 * psi 0 + (blochNormSq r : Complex) * psi 1 := by
        rw [bloch_square_one_off_diagonal, bloch_square_one_diagonal]
      _ = _ := by simp
theorem blochOperator_adjoint (r : PauliAxis -> Real) :
    LinearMap.adjoint (blochOperator r) = blochOperator r := by
  apply LinearMap.IsSymmetric.adjoint_eq
  unfold blochOperator
  apply LinearMap.IsSymmetric.add
  · apply LinearMap.IsSymmetric.add
    · apply LinearMap.IsSymmetric.smul
      · simp
      · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
        exact pauliX_adjoint
    · apply LinearMap.IsSymmetric.smul
      · simp
      · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
        exact pauliY_adjoint
  · apply LinearMap.IsSymmetric.smul
    · simp
    · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
      exact pauliZ_adjoint
theorem blochProjector_idempotent (r : PauliAxis -> Real)
    (hr : blochNormSq r = 1) : blochProjector r * blochProjector r = blochProjector r := by
  have hsquare : blochOperator r * blochOperator r = 1 := by
    rw [blochOperator_square, hr]
    norm_num
  simp only [blochProjector, smul_mul_assoc, mul_smul_comm, smul_smul,
    mul_add, add_mul, one_mul, mul_one, hsquare]
  module
theorem blochProjector_isSymmetricProjection (r : PauliAxis -> Real)
    (hr : blochNormSq r = 1) : (blochProjector r).IsSymmetricProjection := by
  refine ⟨blochProjector_idempotent r hr, ?_⟩
  unfold blochProjector
  apply LinearMap.IsSymmetric.smul
  · simp only [starRingEnd_apply, star_inv₀, star_ofNat]
  · apply LinearMap.IsSymmetric.add
    · exact LinearMap.IsSymmetric.one
    · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
      exact blochOperator_adjoint r
theorem blochProjector_positive (r : PauliAxis -> Real)
    (hr : blochNormSq r = 1) : LinearMap.IsPositive (blochProjector r) :=
  (blochProjector_isSymmetricProjection r hr).isPositive
theorem blochProjector_trace_one (r : PauliAxis -> Real)
    (hr : blochNormSq r = 1) : LinearMap.trace Complex QubitSpace (blochProjector r) = 1 := by
  simp [blochProjector, blochOperator, pauliI_trace, pauliX_trace, pauliY_trace,
    pauliZ_trace]
noncomputable def blochDensity (r : PauliAxis -> Real)
    (hr : blochNormSq r = 1) : DensityOperator QubitSpace where
  toOperator := blochProjector r
  positive := blochProjector_positive r hr
  trace_one := blochProjector_trace_one r hr
noncomputable def tMagicState : DensityOperator QubitSpace :=
  blochDensity tBloch tBloch_normalized
noncomputable def hMagicState : DensityOperator QubitSpace :=
  blochDensity hBloch hBloch_normalized
noncomputable def tMagicStateOfDirection (d : TDirection) : DensityOperator QubitSpace :=
  blochDensity (tBlochOfDirection d) (tBlochOfDirection_normalized d)
noncomputable def hMagicStateOfDirection (d : HDirection) : DensityOperator QubitSpace :=
  blochDensity (hBlochOfDirection d) (hBlochOfDirection_normalized d)
def projectionSquaredOverlap
    (P : Operator QubitSpace) (rho : DensityOperator QubitSpace) : Real :=
  (LinearMap.trace Complex QubitSpace (P * rho.toOperator)).re
def projectionFidelity
    (P : Operator QubitSpace) (rho : DensityOperator QubitSpace) : Real :=
  Real.sqrt (projectionSquaredOverlap P rho)
def tDirectionFidelity
    (rho : DensityOperator QubitSpace) (d : TDirection) : Real :=
  projectionFidelity (tProjector d) rho
def hDirectionFidelity
    (rho : DensityOperator QubitSpace) (d : HDirection) : Real :=
  projectionFidelity (hProjector d) rho
def tFidelity (rho : DensityOperator QubitSpace) : Real :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨tReference⟩)
    (tDirectionFidelity rho)
def hFidelity (rho : DensityOperator QubitSpace) : Real :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨hReference⟩)
    (hDirectionFidelity rho)
theorem exists_tDirection_attaining_fidelity
    (rho : DensityOperator QubitSpace) :
    ∃ d, tFidelity rho = tDirectionFidelity rho d := by
  unfold tFidelity
  obtain ⟨d, _, hd⟩ :=
    Finset.exists_mem_eq_sup'
      (Finset.univ_nonempty_iff.mpr ⟨tReference⟩) (tDirectionFidelity rho)
  exact ⟨d, hd⟩
theorem exists_hDirection_attaining_fidelity
    (rho : DensityOperator QubitSpace) :
    ∃ d, hFidelity rho = hDirectionFidelity rho d := by
  unfold hFidelity
  obtain ⟨d, _, hd⟩ :=
    Finset.exists_mem_eq_sup'
      (Finset.univ_nonempty_iff.mpr ⟨hReference⟩) (hDirectionFidelity rho)
  exact ⟨d, hd⟩
noncomputable def tMaximizingDirection
    (rho : DensityOperator QubitSpace) : TDirection :=
  Classical.choose (exists_tDirection_attaining_fidelity rho)
noncomputable def hMaximizingDirection
    (rho : DensityOperator QubitSpace) : HDirection :=
  Classical.choose (exists_hDirection_attaining_fidelity rho)
end OneQubitMagic
end Distillation
end QEC



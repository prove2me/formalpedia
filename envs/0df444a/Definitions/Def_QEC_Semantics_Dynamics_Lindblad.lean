-- Prove2me | Definitions.Def_QEC_Semantics_Dynamics_Lindblad
-- name    : QEC_Semantics_Dynamics_Lindblad
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:16:54.737772+00:00
-- url     : https://prove2.me/theorems/1f90647a-aafe-4696-a0dd-fa2f62e45668
-- title:
--   Lindblad
-- statement:
--   Definitions and structural lemmas for Lindblad, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_tendsto_lieTrotter
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg


set_option autoImplicit false
universe u v
namespace QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
noncomputable local instance finiteQuantumSystemComplete : CompleteSpace H :=
  FiniteDimensional.complete Complex H
abbrev ContinuousOperator (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] := H →L[Complex] H
abbrev ContinuousSuperoperator (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] :=
  ContinuousOperator H →L[Complex] ContinuousOperator H
abbrev Superoperator (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [FiniteQuantumSystem H] :=
  Operator H →ₗ[Complex] Operator H
noncomputable def continuousLeftRegularRepresentation :
    ContinuousOperator H →+* ContinuousSuperoperator H where
  toFun X := ContinuousLinearMap.mulLeftRight Complex (ContinuousOperator H) X 1
  map_zero' := by
    apply ContinuousLinearMap.ext; intro A
    apply ContinuousLinearMap.ext; intro x
    change (((0 : ContinuousOperator H) * A * 1) x) = 0
    simp
  map_one' := by
    apply ContinuousLinearMap.ext; intro A
    apply ContinuousLinearMap.ext; intro x
    change (((1 : ContinuousOperator H) * A * 1) x) = A x
    simp
  map_add' X Y := by
    apply ContinuousLinearMap.ext; intro A
    apply ContinuousLinearMap.ext; intro x
    change (((X + Y) * A * 1) x) = ((X * A * 1 + Y * A * 1) x)
    simp [add_mul]
  map_mul' X Y := by
    apply ContinuousLinearMap.ext; intro A
    apply ContinuousLinearMap.ext; intro x
    change (((X * Y) * A * 1) x) = (X * (Y * A * 1) * 1) x
    simp [mul_assoc]
noncomputable def continuousRightRegularRepresentation :
    (ContinuousOperator H)ᵐᵒᵖ →+* ContinuousSuperoperator H where
  toFun X := ContinuousLinearMap.mulLeftRight Complex (ContinuousOperator H)
    1 (MulOpposite.unop X)
  map_zero' := by
    apply ContinuousLinearMap.ext; intro A
    apply ContinuousLinearMap.ext; intro x
    change ((1 * A * (0 : ContinuousOperator H)) x) = 0
    simp
  map_one' := by
    apply ContinuousLinearMap.ext; intro A
    apply ContinuousLinearMap.ext; intro x
    change ((1 * A * (1 : ContinuousOperator H)) x) = A x
    simp
  map_add' X Y := by
    apply ContinuousLinearMap.ext; intro A
    apply ContinuousLinearMap.ext; intro x
    change ((1 * A * (MulOpposite.unop X + MulOpposite.unop Y)) x) =
      ((1 * A * MulOpposite.unop X + 1 * A * MulOpposite.unop Y) x)
    simp [mul_add]
  map_mul' X Y := by
    apply ContinuousLinearMap.ext; intro A
    apply ContinuousLinearMap.ext; intro x
    change ((1 * A * (MulOpposite.unop Y * MulOpposite.unop X)) x) =
      (1 * (1 * A * MulOpposite.unop Y) * MulOpposite.unop X) x
    simp [mul_assoc]
@[simp]
theorem continuousLeftRegularRepresentation_apply
    (X A : ContinuousOperator H) :
    continuousLeftRegularRepresentation (H := H) X A = X * A := by
  rfl
@[simp]
theorem continuousRightRegularRepresentation_apply
    (X : (ContinuousOperator H)ᵐᵒᵖ) (A : ContinuousOperator H) :
    continuousRightRegularRepresentation (H := H) X A =
      A * MulOpposite.unop X := by
  rfl
theorem continuous_continuousLeftRegularRepresentation :
    Continuous (continuousLeftRegularRepresentation (H := H)) := by
  exact (continuous_const.clm_apply continuous_id).clm_apply continuous_const
theorem continuous_continuousRightRegularRepresentation :
    Continuous (continuousRightRegularRepresentation (H := H)) := by
  exact (continuous_const.clm_apply continuous_const).clm_apply
    MulOpposite.continuous_unop
theorem exp_continuousLeftRegularRepresentation (X : ContinuousOperator H) :
    NormedSpace.exp (continuousLeftRegularRepresentation (H := H) X) =
      continuousLeftRegularRepresentation (H := H) (NormedSpace.exp X) := by
  exact (NormedSpace.map_exp_of_mem_ball
    (continuousLeftRegularRepresentation (H := H))
    continuous_continuousLeftRegularRepresentation X
    ((NormedSpace.expSeries_radius_eq_top Complex (ContinuousOperator H)).symm ▸
      edist_lt_top _ _)).symm
theorem exp_continuousRightRegularRepresentation (X : ContinuousOperator H) :
    NormedSpace.exp
        (continuousRightRegularRepresentation (H := H) (MulOpposite.op X)) =
      continuousRightRegularRepresentation (H := H)
        (MulOpposite.op (NormedSpace.exp X)) := by
  calc
    NormedSpace.exp
        (continuousRightRegularRepresentation (H := H) (MulOpposite.op X)) =
        continuousRightRegularRepresentation (H := H)
          (NormedSpace.exp (MulOpposite.op X)) :=
      (NormedSpace.map_exp_of_mem_ball
        (continuousRightRegularRepresentation (H := H))
        continuous_continuousRightRegularRepresentation (MulOpposite.op X)
        ((NormedSpace.expSeries_radius_eq_top Complex
          ((ContinuousOperator H)ᵐᵒᵖ)).symm ▸ edist_lt_top _ _)).symm
    _ = continuousRightRegularRepresentation (H := H)
        (MulOpposite.op (NormedSpace.exp X)) := by rw [NormedSpace.exp_op]
theorem commute_continuousRegularRepresentations
    (X Y : ContinuousOperator H) :
    Commute (continuousLeftRegularRepresentation (H := H) X)
      (continuousRightRegularRepresentation (H := H) (MulOpposite.op Y)) := by
  apply ContinuousLinearMap.ext
  intro A
  apply ContinuousLinearMap.ext
  intro x
  change (X * (A * Y)) x = ((X * A) * Y) x
  simp [mul_assoc]
noncomputable def continuousOperatorAdjointReal :
    ContinuousOperator H →L[Real] ContinuousOperator H where
  toFun := ContinuousLinearMap.adjoint
  map_add' A B := by
    exact ContinuousLinearMap.adjoint.map_add A B
  map_smul' r A := by
    change ContinuousLinearMap.adjoint ((r : Complex) • A) =
      (r : Complex) • ContinuousLinearMap.adjoint A
    rw [map_smulₛₗ]
    have hr : (starRingEnd Complex) (r : Complex) = (r : Complex) := by
      apply Complex.ext <;> simp
    rw [hr]
  cont := ContinuousLinearMap.adjoint.continuous
def lindbladJumpTerm (J : Operator H) : Superoperator H where
  toFun A := J * A * LinearMap.adjoint J -
    (2 : Complex)⁻¹ •
      ((LinearMap.adjoint J * J) * A + A * (LinearMap.adjoint J * J))
  map_add' A B := by
    ext x
    simp [mul_add, add_mul]
    module
  map_smul' c A := by
    ext x
    simp
    module
theorem lindbladJumpTerm_apply (J A : Operator H) :
    lindbladJumpTerm J A = J * A * LinearMap.adjoint J -
      (2 : Complex)⁻¹ •
        ((LinearMap.adjoint J * J) * A + A * (LinearMap.adjoint J * J)) :=
  rfl
def lindbladDissipator [Fintype ι]
    (J : ι → Operator H) : Superoperator H :=
  ∑ a, lindbladJumpTerm (J a)
theorem lindbladDissipator_apply [Fintype ι]
    (J : ι → Operator H) (A : Operator H) :
    lindbladDissipator J A = ∑ a, lindbladJumpTerm (J a) A := by
  simp [lindbladDissipator]
def lindbladJumpGain [Fintype ι] (J : ι → Operator H) : Superoperator H where
  toFun A := ∑ a, J a * A * LinearMap.adjoint (J a)
  map_add' A B := by
    ext x
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    ext x
    simp
    simp only [Finset.smul_sum]
theorem lindbladJumpGain_apply [Fintype ι]
    (J : ι → Operator H) (A : Operator H) :
    lindbladJumpGain J A = ∑ a, J a * A * LinearMap.adjoint (J a) :=
  rfl
def lindbladJumpKrausFamily [Fintype ι]
    (J : ι → Operator H) : FiniteKrausFamily ι H H where
  operator := J
theorem lindbladJumpGain_eq_inducedMap [Fintype ι] (J : ι → Operator H) :
    lindbladJumpGain J = (lindbladJumpKrausFamily J).inducedMap := by
  ext A x
  simp [lindbladJumpGain, lindbladJumpKrausFamily,
    FiniteKrausFamily.inducedMap_apply, mul_assoc]
theorem lindbladJumpGain_completelyPositive [Fintype ι] (J : ι → Operator H) :
    CompletelyPositive (lindbladJumpGain J) := by
  rw [lindbladJumpGain_eq_inducedMap]
  exact (lindbladJumpKrausFamily J).inducedMap_completelyPositive
def singleKrausMap (V : Operator H) : Superoperator H where
  toFun A := V * A * LinearMap.adjoint V
  map_add' A B := by
    ext x
    simp [mul_add]
  map_smul' c A := by
    ext x
    simp
def singleKrausFamily (V : Operator H) : FiniteKrausFamily Unit H H where
  operator _ := V
theorem singleKrausMap_eq_inducedMap (V : Operator H) :
    singleKrausMap V = (singleKrausFamily V).inducedMap := by
  ext A x
  simp [singleKrausMap, singleKrausFamily,
    FiniteKrausFamily.inducedMap_apply, mul_assoc]
theorem singleKrausMap_completelyPositive (V : Operator H) :
    CompletelyPositive (singleKrausMap V) := by
  rw [singleKrausMap_eq_inducedMap]
  exact (singleKrausFamily V).inducedMap_completelyPositive
namespace CompletelyPositive
variable {K L : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
theorem comp {Φ : Operator H →ₗ[Complex] Operator K}
    {Ψ : Operator K →ₗ[Complex] Operator L}
    (hΦ : CompletelyPositive Φ) (hΨ : CompletelyPositive Ψ) :
    CompletelyPositive (Ψ.comp Φ) := by
  intro n M hM
  exact hΨ n (OperatorMatrix.map Φ M) (hΦ n M hM)
theorem nonneg_smul (c : Real) (hc : 0 ≤ c)
    {Φ : Operator H →ₗ[Complex] Operator K}
    (hΦ : CompletelyPositive Φ) :
    CompletelyPositive ((c : Complex) • Φ) := by
  intro n M hM
  constructor
  · intro i j
    simp only [OperatorMatrix.map, LinearMap.smul_apply, map_smulₛₗ]
    have hcstar : (starRingEnd Complex) (c : Complex) = (c : Complex) := by
      apply Complex.ext <;> simp
    rw [hcstar]
    exact congrArg ((c : Complex) • ·) ((hΦ n M hM).1 i j)
  · intro x
    have hp := (hΦ n M hM).2 x
    have hnonneg : 0 ≤ c * Complex.re
        (∑ i : Fin n, ∑ j : Fin n, inner Complex (Φ (M i j) (x j)) (x i)) :=
      mul_nonneg hc hp
    simp only [OperatorMatrix.map, LinearMap.smul_apply, inner_smul_left]
    have hcstar : (starRingEnd Complex) (c : Complex) = (c : Complex) := by
      apply Complex.ext <;> simp
    rw [hcstar]
    have heq :
        (∑ i : Fin n, ∑ j : Fin n,
          (c : Complex) * inner Complex (Φ (M i j) (x j)) (x i)) =
        (c : Complex) * (∑ i : Fin n, ∑ j : Fin n,
          inner Complex (Φ (M i j) (x j)) (x i)) := by
      symm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
    rw [heq]
    simpa only [Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using hnonneg
theorem zero :
    CompletelyPositive (0 : Operator H →ₗ[Complex] Operator K) := by
  intro n M hM
  constructor
  · intro i j
    simp [OperatorMatrix.map]
  · intro x
    simp [OperatorMatrix.map]
end CompletelyPositive
def hamiltonianCommutator (hamiltonian : Operator H) : Superoperator H where
  toFun A := (-Complex.I) • (hamiltonian * A - A * hamiltonian)
  map_add' A B := by
    ext x
    simp [mul_add, add_mul]
    module
  map_smul' c A := by
    ext x
    simp
    module
theorem hamiltonianCommutator_apply (hamiltonian A : Operator H) :
    hamiltonianCommutator hamiltonian A =
      (-Complex.I) • (hamiltonian * A - A * hamiltonian) :=
  rfl
def finiteLindbladGenerator [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) : Superoperator H :=
  hamiltonianCommutator hamiltonian + lindbladDissipator J
def lindbladLossOperator [Fintype ι] (J : ι → Operator H) : Operator H :=
  ∑ a, LinearMap.adjoint (J a) * J a
def lindbladEffectiveOperator [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) : Operator H :=
  (-Complex.I) • hamiltonian -
    (2 : Complex)⁻¹ • lindbladLossOperator J
def lindbladNoJumpDrift (K : Operator H) : Superoperator H where
  toFun A := K * A + A * LinearMap.adjoint K
  map_add' A B := by
    ext x
    simp [mul_add, add_mul]
    module
  map_smul' c A := by
    ext x
    simp
theorem lindbladNoJumpDrift_apply (K A : Operator H) :
    lindbladNoJumpDrift K A = K * A + A * LinearMap.adjoint K :=
  rfl
theorem adjoint_lindbladLossOperator [Fintype ι] (J : ι → Operator H) :
    LinearMap.adjoint (lindbladLossOperator J) = lindbladLossOperator J := by
  classical
  rw [lindbladLossOperator, map_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Module.End.mul_eq_comp, LinearMap.adjoint_comp,
    LinearMap.adjoint_adjoint, ← Module.End.mul_eq_comp]
theorem adjoint_lindbladEffectiveOperator [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (hhamiltonian : hamiltonian.IsSymmetric) :
    LinearMap.adjoint (lindbladEffectiveOperator hamiltonian J) =
      Complex.I • hamiltonian -
        (2 : Complex)⁻¹ • lindbladLossOperator J := by
  rw [lindbladEffectiveOperator]
  rw [map_sub]
  rw [map_smulₛₗ, map_smulₛₗ]
  rw [hhamiltonian.adjoint_eq, adjoint_lindbladLossOperator]
  have htwo : (starRingEnd Complex) ((2 : Complex)⁻¹) = (2 : Complex)⁻¹ := by
    apply Complex.ext <;> norm_num
  have hI : (starRingEnd Complex) (-Complex.I) = Complex.I := by
    apply Complex.ext <;> norm_num
  rw [hI]
  rw [htwo]
theorem lindbladNoJumpDrift_effective_apply [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (hhamiltonian : hamiltonian.IsSymmetric) (A : Operator H) :
    lindbladNoJumpDrift (lindbladEffectiveOperator hamiltonian J) A =
      lindbladEffectiveOperator hamiltonian J * A +
        A * (Complex.I • hamiltonian -
          (2 : Complex)⁻¹ • lindbladLossOperator J) := by
  rw [lindbladNoJumpDrift_apply,
    adjoint_lindbladEffectiveOperator hamiltonian J hhamiltonian]
theorem finiteLindbladGenerator_eq_noJump_add_gain [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (hhamiltonian : hamiltonian.IsSymmetric) :
    finiteLindbladGenerator hamiltonian J =
      lindbladNoJumpDrift (lindbladEffectiveOperator hamiltonian J) +
        lindbladJumpGain J := by
  classical
  ext A x
  simp only [finiteLindbladGenerator, LinearMap.add_apply]
  rw [lindbladNoJumpDrift_effective_apply hamiltonian J hhamiltonian]
  simp only [hamiltonianCommutator_apply, lindbladDissipator_apply,
    lindbladJumpTerm_apply, lindbladJumpGain_apply,
    lindbladEffectiveOperator, lindbladLossOperator]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_eq_comp, LinearMap.comp_apply, LinearMap.sum_apply]
  simp only [map_sub, map_smul, map_sum]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_add_distrib]
  module
theorem continuousOperator_adjoint_exp (A : ContinuousOperator H) :
    ContinuousLinearMap.adjoint (NormedSpace.exp A) =
      NormedSpace.exp (ContinuousLinearMap.adjoint A) := by
  change star (NormedSpace.exp A) = NormedSpace.exp (star A)
  exact NormedSpace.star_exp A
noncomputable def lindbladNoJumpPropagatorContinuous
    (K : Operator H) (t : Real) : ContinuousOperator H :=
  NormedSpace.exp ((t : Complex) • LinearMap.toContinuousLinearMap K)
noncomputable def lindbladNoJumpPropagator
    (K : Operator H) (t : Real) : Operator H :=
  (lindbladNoJumpPropagatorContinuous K t).toLinearMap
noncomputable def lindbladNoJumpEvolutionLinearMap
    (K : Operator H) (t : Real) : Superoperator H :=
  singleKrausMap (lindbladNoJumpPropagator K t)
theorem lindbladNoJumpEvolutionLinearMap_completelyPositive
    (K : Operator H) (t : Real) :
    CompletelyPositive (lindbladNoJumpEvolutionLinearMap K t) :=
  singleKrausMap_completelyPositive (lindbladNoJumpPropagator K t)
@[simp]
theorem lindbladNoJumpPropagatorContinuous_zero (K : Operator H) :
    lindbladNoJumpPropagatorContinuous K 0 = 1 := by
  unfold lindbladNoJumpPropagatorContinuous
  have hz : ((0 : Real) : Complex) • LinearMap.toContinuousLinearMap K = 0 := by
    simp
  rw [hz, NormedSpace.exp_zero]
@[simp]
theorem lindbladNoJumpPropagator_zero (K : Operator H) :
    lindbladNoJumpPropagator K 0 = 1 := by
  unfold lindbladNoJumpPropagator
  rw [lindbladNoJumpPropagatorContinuous_zero]
  rfl
@[simp]
theorem lindbladNoJumpEvolutionLinearMap_zero (K : Operator H) :
    lindbladNoJumpEvolutionLinearMap K 0 = LinearMap.id := by
  ext A x
  simp [lindbladNoJumpEvolutionLinearMap, singleKrausMap,
    lindbladNoJumpPropagator_zero]
theorem adjoint_lindbladNoJumpPropagatorContinuous
    (K : Operator H) (t : Real) :
    ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t) =
      NormedSpace.exp ((t : Complex) •
        ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)) := by
  unfold lindbladNoJumpPropagatorContinuous
  rw [continuousOperator_adjoint_exp]
  rw [map_smulₛₗ]
  have ht : (starRingEnd Complex) (t : Complex) = (t : Complex) := by
    apply Complex.ext <;> simp
  rw [ht]
noncomputable def lindbladNoJumpTrajectoryContinuous
    (K : Operator H) (A : ContinuousOperator H) (t : Real) :
    ContinuousOperator H :=
  lindbladNoJumpPropagatorContinuous K t * A *
    ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t)
noncomputable def lindbladNoJumpEvolutionContinuous
    (K : Operator H) (t : Real) : ContinuousSuperoperator H :=
  ContinuousLinearMap.mulLeftRight Complex (ContinuousOperator H)
    (lindbladNoJumpPropagatorContinuous K t)
    (ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t))
@[simp]
theorem lindbladNoJumpEvolutionContinuous_apply
    (K : Operator H) (t : Real) (A : ContinuousOperator H) :
    lindbladNoJumpEvolutionContinuous K t A =
      lindbladNoJumpTrajectoryContinuous K A t :=
  rfl
@[simp]
theorem lindbladNoJumpEvolutionContinuous_zero (K : Operator H) :
    lindbladNoJumpEvolutionContinuous K 0 = 1 := by
  ext A x
  simp [lindbladNoJumpEvolutionContinuous,
    lindbladNoJumpPropagatorContinuous_zero, ContinuousLinearMap.adjoint_one]
theorem trace_lindbladJumpTerm (J A : Operator H) :
    LinearMap.trace Complex H (lindbladJumpTerm J A) = 0 := by
  have hcycle :
      LinearMap.trace Complex H (J * A * LinearMap.adjoint J) =
        LinearMap.trace Complex H ((LinearMap.adjoint J * J) * A) := by
    calc
      LinearMap.trace Complex H (J * A * LinearMap.adjoint J) =
          LinearMap.trace Complex H (LinearMap.adjoint J * (J * A)) := by
        exact LinearMap.trace_mul_comm (R := Complex) (M := H)
          (J * A) (LinearMap.adjoint J)
      _ = LinearMap.trace Complex H ((LinearMap.adjoint J * J) * A) := by
        exact congrArg (LinearMap.trace Complex H)
          (mul_assoc (LinearMap.adjoint J) J A).symm
  have hcycle' :
      LinearMap.trace Complex H (A * (LinearMap.adjoint J * J)) =
        LinearMap.trace Complex H ((LinearMap.adjoint J * J) * A) :=
    LinearMap.trace_mul_comm (R := Complex) (M := H)
      A (LinearMap.adjoint J * J)
  unfold lindbladJumpTerm
  dsimp
  rw [map_sub, map_smul, map_add, hcycle, hcycle']
  ring
theorem trace_hamiltonianCommutator (hamiltonian A : Operator H) :
    LinearMap.trace Complex H (hamiltonianCommutator hamiltonian A) = 0 := by
  unfold hamiltonianCommutator
  dsimp
  rw [map_smul, map_sub,
    LinearMap.trace_mul_comm (R := Complex) (M := H) hamiltonian A]
  ring
theorem trace_finiteLindbladGenerator [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (A : Operator H) :
    LinearMap.trace Complex H (finiteLindbladGenerator hamiltonian J A) = 0 := by
  simp [finiteLindbladGenerator, lindbladDissipator,
    trace_hamiltonianCommutator, trace_lindbladJumpTerm]
noncomputable def continuousOperatorTrace : ContinuousOperator H →L[Complex] Complex :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => LinearMap.trace Complex H A.toLinearMap
      map_add' := by intro A B; simp
      map_smul' := by intro c A; simp }
noncomputable def asContinuousSuperoperator (L : Superoperator H) :
    ContinuousSuperoperator H :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      (L.comp LinearMap.toContinuousLinearMap.symm.toLinearMap))
noncomputable def asOperatorSuperoperator (L : ContinuousSuperoperator H) :
    Superoperator H :=
  LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
    (L.toLinearMap.comp LinearMap.toContinuousLinearMap.toLinearMap)
@[simp]
theorem asContinuousSuperoperator_add (L M : Superoperator H) :
    asContinuousSuperoperator (L + M) =
      asContinuousSuperoperator L + asContinuousSuperoperator M := by
  apply ContinuousLinearMap.ext
  intro A
  apply ContinuousLinearMap.ext
  intro x
  rfl
theorem asContinuousSuperoperator_lindbladNoJumpDrift (K : Operator H) :
    asContinuousSuperoperator (lindbladNoJumpDrift K) =
      continuousLeftRegularRepresentation (H := H)
          (LinearMap.toContinuousLinearMap K) +
        continuousRightRegularRepresentation (H := H)
          (MulOpposite.op
            (ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K))) := by
  apply ContinuousLinearMap.ext
  intro A
  apply ContinuousLinearMap.ext
  intro x
  change
    (LinearMap.toContinuousLinearMap K * A +
      A * ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)) x = _
  rfl
@[simp]
theorem asOperatorSuperoperator_one :
    asOperatorSuperoperator (1 : ContinuousSuperoperator H) = LinearMap.id := by
  ext A x
  rfl
@[simp]
theorem asOperatorSuperoperator_mul (L M : ContinuousSuperoperator H) :
    asOperatorSuperoperator (L * M) =
      (asOperatorSuperoperator L).comp (asOperatorSuperoperator M) := by
  ext A x
  rfl
@[simp]
theorem asOperatorSuperoperator_smul (c : Complex)
    (L : ContinuousSuperoperator H) :
    asOperatorSuperoperator (c • L) =
      c • asOperatorSuperoperator L := by
  ext A x
  rfl
@[simp]
theorem asOperatorSuperoperator_asContinuousSuperoperator (L : Superoperator H) :
    asOperatorSuperoperator (asContinuousSuperoperator L) = L := by
  ext A x
  rfl
theorem asOperatorSuperoperator_lindbladNoJumpEvolutionContinuous
    (K : Operator H) (t : Real) :
    asOperatorSuperoperator (lindbladNoJumpEvolutionContinuous K t) =
      lindbladNoJumpEvolutionLinearMap K t := by
  ext A x
  change
    (lindbladNoJumpPropagatorContinuous K t *
      LinearMap.toContinuousLinearMap A *
      ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t)) x =
    (lindbladNoJumpPropagator K t * A *
      LinearMap.adjoint (lindbladNoJumpPropagator K t)) x
  unfold lindbladNoJumpPropagator
  rw [LinearMap.adjoint_eq_toCLM_adjoint]
  rfl
theorem lindbladNoJumpEvolutionContinuous_completelyPositive
    (K : Operator H) (t : Real) :
    CompletelyPositive
      (asOperatorSuperoperator (lindbladNoJumpEvolutionContinuous K t)) := by
  rw [asOperatorSuperoperator_lindbladNoJumpEvolutionContinuous]
  exact lindbladNoJumpEvolutionLinearMap_completelyPositive K t
theorem exp_asContinuousSuperoperator_lindbladNoJumpDrift
    (K : Operator H) (t : Real) :
    NormedSpace.exp
        ((t : Complex) • asContinuousSuperoperator (lindbladNoJumpDrift K)) =
      lindbladNoJumpEvolutionContinuous K t := by
  let Kc := LinearMap.toContinuousLinearMap K
  let Kadj := ContinuousLinearMap.adjoint Kc
  have hscaled :
      (t : Complex) • asContinuousSuperoperator (lindbladNoJumpDrift K) =
        continuousLeftRegularRepresentation (H := H) ((t : Complex) • Kc) +
          continuousRightRegularRepresentation (H := H)
            (MulOpposite.op ((t : Complex) • Kadj)) := by
    rw [asContinuousSuperoperator_lindbladNoJumpDrift]
    apply ContinuousLinearMap.ext
    intro A
    apply ContinuousLinearMap.ext
    intro x
    simp
    rfl
  rw [hscaled, NormedSpace.exp_add_of_commute_of_mem_ball
    (commute_continuousRegularRepresentations ((t : Complex) • Kc)
      ((t : Complex) • Kadj))
    ((NormedSpace.expSeries_radius_eq_top Complex
      (ContinuousSuperoperator H)).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top Complex
      (ContinuousSuperoperator H)).symm ▸ edist_lt_top _ _)]
  rw [exp_continuousLeftRegularRepresentation,
    exp_continuousRightRegularRepresentation]
  apply ContinuousLinearMap.ext
  intro A
  apply ContinuousLinearMap.ext
  intro x
  change
    (NormedSpace.exp ((t : Complex) • Kc) * A *
      NormedSpace.exp ((t : Complex) • Kadj)) x =
      (lindbladNoJumpPropagatorContinuous K t * A *
        ContinuousLinearMap.adjoint
          (lindbladNoJumpPropagatorContinuous K t)) x
  rw [adjoint_lindbladNoJumpPropagatorContinuous]
  rfl
noncomputable def lindbladJumpGainContinuous [Fintype ι]
    (J : ι → Operator H) : ContinuousSuperoperator H :=
  asContinuousSuperoperator (lindbladJumpGain J)
@[simp]
theorem asOperatorSuperoperator_lindbladJumpGainContinuous [Fintype ι]
    (J : ι → Operator H) :
    asOperatorSuperoperator (lindbladJumpGainContinuous J) =
      lindbladJumpGain J := by
  exact asOperatorSuperoperator_asContinuousSuperoperator (lindbladJumpGain J)
noncomputable def lindbladDysonIntegrandContinuous [Fintype ι]
    (K : Operator H) (J : ι → Operator H)
    (previous : Real → ContinuousSuperoperator H) (t s : Real) :
    ContinuousSuperoperator H :=
  lindbladNoJumpEvolutionContinuous K (t - s) *
    lindbladJumpGainContinuous J * previous s
noncomputable def lindbladDysonTermContinuous [Fintype ι]
    (K : Operator H) (J : ι → Operator H) :
    Nat → Real → ContinuousSuperoperator H
  | 0, t => lindbladNoJumpEvolutionContinuous K t
  | n + 1, t => ∫ s in (0 : Real)..t,
      lindbladDysonIntegrandContinuous K J
        (lindbladDysonTermContinuous K J n) t s
noncomputable def lindbladDysonPartialSumContinuous [Fintype ι]
    (K : Operator H) (J : ι → Operator H) (N : Nat) (t : Real) :
    ContinuousSuperoperator H :=
  ∑ n ∈ Finset.range (N + 1), lindbladDysonTermContinuous K J n t
noncomputable def lindbladDysonEvolutionContinuous [Fintype ι]
    (K : Operator H) (J : ι → Operator H) (t : Real) :
    ContinuousSuperoperator H :=
  ∑' n, lindbladDysonTermContinuous K J n t
@[simp]
theorem lindbladDysonTermContinuous_zero [Fintype ι]
    (K : Operator H) (J : ι → Operator H) (t : Real) :
    lindbladDysonTermContinuous K J 0 t =
      lindbladNoJumpEvolutionContinuous K t :=
  rfl
set_option maxHeartbeats 800000 in
theorem tsum_preserves_adjoint_blocks
    (f : Nat → ContinuousSuperoperator H) (hf : Summable f)
    (A B : Operator H)
    (hsym : ∀ n, asOperatorSuperoperator (f n) B =
      LinearMap.adjoint (asOperatorSuperoperator (f n) A)) :
    asOperatorSuperoperator (∑' n, f n) B =
      LinearMap.adjoint (asOperatorSuperoperator (∑' n, f n) A) := by
  let Ac := LinearMap.toContinuousLinearMap A
  let Bc := LinearMap.toContinuousLinearMap B
  let evalA :=
    (ContinuousLinearMap.apply Complex (ContinuousOperator H) Ac).restrictScalars Real
  let evalB :=
    (ContinuousLinearMap.apply Complex (ContinuousOperator H) Bc).restrictScalars Real
  have hfA : Summable (fun n => f n Ac) := evalA.summable hf
  have hs (n : Nat) :
      f n Bc = ContinuousLinearMap.adjoint (f n Ac) := by
    apply ContinuousLinearMap.ext
    intro x
    have h := congrArg (fun T : Operator H => T x) (hsym n)
    rw [LinearMap.adjoint_eq_toCLM_adjoint] at h
    exact h
  have hcontinuous :
      (∑' n, f n Bc) =
        ContinuousLinearMap.adjoint (∑' n, f n Ac) := by
    calc
      (∑' n, f n Bc) =
          (∑' n, ContinuousLinearMap.adjoint (f n Ac)) := by
            congr 1
            funext n
            exact hs n
      _ = ContinuousLinearMap.adjoint (∑' n, f n Ac) := by
            exact (continuousOperatorAdjointReal.map_tsum hfA).symm
  rw [LinearMap.adjoint_eq_toCLM_adjoint]
  apply congrArg ContinuousLinearMap.toLinearMap
  change (∑' n, f n) Bc =
    ContinuousLinearMap.adjoint ((∑' n, f n) Ac)
  change evalB (∑' n, f n) =
    ContinuousLinearMap.adjoint (evalA (∑' n, f n))
  rw [evalB.map_tsum hf, evalA.map_tsum hf]
  exact hcontinuous
set_option synthInstance.maxHeartbeats 200000 in
/-- The block quadratic form as a real continuous functional of a superoperator. -/
noncomputable def completelyPositiveQuadraticFunctional (n : Nat)
    (M : OperatorMatrix n H) (x : Fin n → H) :
    ContinuousSuperoperator H →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun L => Complex.re
        (∑ i : Fin n, ∑ j : Fin n,
          inner Complex (L (LinearMap.toContinuousLinearMap (M i j)) (x j)) (x i))
      map_add' := by
        intro L N
        simp only [ContinuousLinearMap.add_apply, inner_add_left,
          Complex.add_re, Finset.sum_add_distrib]
      map_smul' := by
        intro r L
        simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply]
        have heq :
            (∑ i : Fin n, ∑ j : Fin n,
              inner Complex
                (r • (L (LinearMap.toContinuousLinearMap (M i j))) (x j)) (x i)) =
            (r : Complex) * (∑ i : Fin n, ∑ j : Fin n,
              inner Complex
                (L (LinearMap.toContinuousLinearMap (M i j)) (x j)) (x i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          change inner Complex
            ((r : Complex) •
              (L (LinearMap.toContinuousLinearMap (M i j))) (x j)) (x i) = _
          rw [inner_smul_left]
          simp
        rw [heq, Complex.mul_re]
        simp }
theorem completelyPositiveQuadraticFunctional_apply (n : Nat)
    (M : OperatorMatrix n H) (x : Fin n → H)
    (L : ContinuousSuperoperator H) :
    completelyPositiveQuadraticFunctional n M x L =
      Complex.re (∑ i : Fin n, ∑ j : Fin n,
        inner Complex
          (asOperatorSuperoperator L (M i j) (x j)) (x i)) := by
  simp [completelyPositiveQuadraticFunctional, asOperatorSuperoperator]
namespace CompletelyPositive
set_option maxHeartbeats 800000 in
theorem tsum
    (f : Nat → ContinuousSuperoperator H) (hf : Summable f)
    (hcp : ∀ n, CompletelyPositive (asOperatorSuperoperator (f n))) :
    CompletelyPositive (asOperatorSuperoperator (∑' n, f n)) := by
  intro n M hM
  constructor
  · intro i j
    exact tsum_preserves_adjoint_blocks f hf (M i j) (M j i)
      (fun k => (hcp k n M hM).1 i j)
  · intro x
    let q := completelyPositiveQuadraticFunctional n M x
    have hq : Summable (fun k => q (f k)) := q.summable hf
    have hnonneg : 0 ≤ ∑' k, q (f k) :=
      tsum_nonneg fun k => by
        simpa [q, completelyPositiveQuadraticFunctional_apply, OperatorMatrix.map] using
          (hcp k n M hM).2 x
    rw [← q.map_tsum hf] at hnonneg
    simpa [q, completelyPositiveQuadraticFunctional_apply, OperatorMatrix.map] using hnonneg
theorem tendsto
    (f : Nat → ContinuousSuperoperator H) (L : ContinuousSuperoperator H)
    (hf : Filter.Tendsto f Filter.atTop (nhds L))
    (hcp : ∀ n, CompletelyPositive (asOperatorSuperoperator (f n))) :
    CompletelyPositive (asOperatorSuperoperator L) := by
  intro n M hM
  constructor
  · intro i j
    let Ac := LinearMap.toContinuousLinearMap (M i j)
    let Bc := LinearMap.toContinuousLinearMap (M j i)
    let evalA := ContinuousLinearMap.apply Complex (ContinuousOperator H) Ac
    let evalB := ContinuousLinearMap.apply Complex (ContinuousOperator H) Bc
    have hA : Filter.Tendsto (fun k => f k Ac) Filter.atTop (nhds (L Ac)) :=
      evalA.continuous.continuousAt.tendsto.comp hf
    have hB : Filter.Tendsto (fun k => f k Bc) Filter.atTop (nhds (L Bc)) :=
      evalB.continuous.continuousAt.tendsto.comp hf
    have hadj : Filter.Tendsto
        (fun k => ContinuousLinearMap.adjoint (f k Ac)) Filter.atTop
        (nhds (ContinuousLinearMap.adjoint (L Ac))) :=
      continuousOperatorAdjointReal.continuous.continuousAt.tendsto.comp hA
    have hterm (k : Nat) :
        f k Bc = ContinuousLinearMap.adjoint (f k Ac) := by
      have hraw := (hcp k n M hM).1 i j
      simp only [OperatorMatrix.map] at hraw
      apply ContinuousLinearMap.ext
      intro x
      have h := congrArg (fun T : Operator H => T x) hraw
      rw [LinearMap.adjoint_eq_toCLM_adjoint] at h
      exact h
    have hcontinuous : L Bc = ContinuousLinearMap.adjoint (L Ac) :=
      tendsto_nhds_unique hB
        (hadj.congr' (Filter.Eventually.of_forall fun k => (hterm k).symm))
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    apply congrArg ContinuousLinearMap.toLinearMap
    simpa [asOperatorSuperoperator, Ac, Bc, OperatorMatrix.map,
      ← LinearMap.coe_toContinuousLinearMap_symm] using hcontinuous
  · intro x
    let q := completelyPositiveQuadraticFunctional n M x
    have hq : Filter.Tendsto (fun k => q (f k)) Filter.atTop (nhds (q L)) :=
      q.continuous.continuousAt.tendsto.comp hf
    have hevent : ∀ᶠ k in Filter.atTop, 0 ≤ q (f k) :=
      Filter.Eventually.of_forall fun k => by
        simpa [q, completelyPositiveQuadraticFunctional_apply, OperatorMatrix.map] using
          (hcp k n M hM).2 x
    have hnonneg : 0 ≤ q L := ge_of_tendsto hq hevent
    simpa [q, completelyPositiveQuadraticFunctional_apply, OperatorMatrix.map] using hnonneg
theorem oneContinuousSuperoperator :
    CompletelyPositive
      (asOperatorSuperoperator (1 : ContinuousSuperoperator H)) := by
  rw [asOperatorSuperoperator_one]
  exact (QuantumChannel.id H).completely_positive
theorem powContinuousSuperoperator (L : ContinuousSuperoperator H)
    (hL : CompletelyPositive (asOperatorSuperoperator L)) (n : Nat) :
    CompletelyPositive (asOperatorSuperoperator (L ^ n)) := by
  induction n with
  | zero => simpa using oneContinuousSuperoperator (H := H)
  | succ n ih =>
      rw [pow_succ, asOperatorSuperoperator_mul]
      exact CompletelyPositive.comp hL ih
theorem expContinuousSuperoperator (L : ContinuousSuperoperator H)
    (hL : CompletelyPositive (asOperatorSuperoperator L)) :
    CompletelyPositive (asOperatorSuperoperator (NormedSpace.exp L)) := by
  rw [← (NormedSpace.exp_series_hasSum_exp' (𝕂 := Complex) L).tsum_eq]
  apply CompletelyPositive.tsum _
    (NormedSpace.expSeries_summable' (𝕂 := Complex) L)
  intro n
  rw [asOperatorSuperoperator_smul]
  simpa using CompletelyPositive.nonneg_smul
    ((Nat.factorial n : Real)⁻¹) (by positivity)
      (powContinuousSuperoperator L hL n)
end CompletelyPositive
noncomputable def selfAdjointTraceNormOneToOne (L : Superoperator H) : Real :=
  sSup {r : Real | ∃ A : Operator H,
    A.IsSymmetric ∧ traceNorm A ≤ 1 ∧ r = traceNorm (L A)}
noncomputable def lindbladDissipatorNorm [Fintype ι]
    (J : ι → Operator H) : Real :=
  selfAdjointTraceNormOneToOne (lindbladDissipator J)
noncomputable def finiteLindbladEvolutionContinuous [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (z : Complex) :
    ContinuousSuperoperator H :=
  NormedSpace.exp
    (z • asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J))
noncomputable def finiteLindbladEvolutionLinearMap [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (t : Real) :
    Superoperator H :=
  asOperatorSuperoperator
    (finiteLindbladEvolutionContinuous hamiltonian J (t : Complex))
theorem finiteLindbladEvolutionLinearMap_completelyPositive_of_nontrivial
    [Fintype ι] [Nontrivial H]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (hhamiltonian : hamiltonian.IsSymmetric)
    (t : Real) (ht : 0 ≤ t) :
    CompletelyPositive (finiteLindbladEvolutionLinearMap hamiltonian J t) := by
  let K := lindbladEffectiveOperator hamiltonian J
  let D := asContinuousSuperoperator (lindbladNoJumpDrift K)
  let G := lindbladJumpGainContinuous J
  let X : ContinuousSuperoperator H := (t : Complex) • D
  let Y : ContinuousSuperoperator H := (t : Complex) • G
  have hgenerator :
      asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J) =
        D + G := by
    rw [finiteLindbladGenerator_eq_noJump_add_gain hamiltonian J hhamiltonian,
      asContinuousSuperoperator_add]
    rfl
  have hevolution :
      finiteLindbladEvolutionContinuous hamiltonian J (t : Complex) =
        NormedSpace.exp (X + Y) := by
    unfold finiteLindbladEvolutionContinuous
    rw [hgenerator]
    change NormedSpace.exp ((t : Complex) • (D + G)) = _
    rw [smul_add]
  rw [finiteLindbladEvolutionLinearMap, hevolution]
  apply CompletelyPositive.tendsto
    (fun n : Nat => (lieTrotterStep X Y ((n : Complex)⁻¹)) ^ n)
    (NormedSpace.exp (X + Y)) (tendsto_lieTrotter X Y)
  intro n
  apply CompletelyPositive.powContinuousSuperoperator
  rw [lieTrotterStep, asOperatorSuperoperator_mul]
  apply CompletelyPositive.comp
  · have hscalar :
        ((n : Complex)⁻¹) • Y =
          ((((n : Real)⁻¹ * t : Real) : Complex) • G) := by
      simp [Y, smul_smul]
    apply CompletelyPositive.expContinuousSuperoperator
    rw [hscalar, asOperatorSuperoperator_smul]
    exact CompletelyPositive.nonneg_smul ((n : Real)⁻¹ * t)
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) ht) (by
          dsimp [G]
          rw [asOperatorSuperoperator_lindbladJumpGainContinuous]
          exact lindbladJumpGain_completelyPositive J)
  · have hscalar :
        ((n : Complex)⁻¹) • X =
          ((((n : Real)⁻¹ * t : Real) : Complex) • D) := by
      simp [X, smul_smul]
    rw [hscalar, exp_asContinuousSuperoperator_lindbladNoJumpDrift]
    exact lindbladNoJumpEvolutionContinuous_completelyPositive K
      ((n : Real)⁻¹ * t)
theorem finiteLindbladEvolutionLinearMap_completelyPositive [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (hhamiltonian : hamiltonian.IsSymmetric)
    (t : Real) (ht : 0 ≤ t) :
    CompletelyPositive (finiteLindbladEvolutionLinearMap hamiltonian J t) := by
  classical
  by_cases hH : Nontrivial H
  · letI := hH
    exact finiteLindbladEvolutionLinearMap_completelyPositive_of_nontrivial
      hamiltonian J hhamiltonian t ht
  · letI : Subsingleton H := not_nontrivial_iff_subsingleton.mp hH
    have hzero : finiteLindbladEvolutionLinearMap hamiltonian J t = 0 := by
      apply LinearMap.ext
      intro A
      apply LinearMap.ext
      intro x
      exact Subsingleton.elim _ _
    rw [hzero]
    exact CompletelyPositive.zero
@[simp]
theorem finiteLindbladEvolutionContinuous_zero [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) :
    finiteLindbladEvolutionContinuous hamiltonian J 0 = 1 := by
  unfold finiteLindbladEvolutionContinuous
  have hz : (0 : Complex) •
      asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J) = 0 := by
    ext A x
    simp
  rw [hz, NormedSpace.exp_zero]
theorem continuousOperatorTrace_generator_eq_zero [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (A : ContinuousOperator H) :
    continuousOperatorTrace
      (asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J) A) = 0 := by
  change LinearMap.trace Complex H
    (finiteLindbladGenerator hamiltonian J A.toLinearMap) = 0
  exact trace_finiteLindbladGenerator hamiltonian J A.toLinearMap
theorem hasDerivAt_trace_finiteLindbladEvolutionContinuous [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (A : ContinuousOperator H) (z : Complex) :
    HasDerivAt
      (fun w => continuousOperatorTrace
        (finiteLindbladEvolutionContinuous hamiltonian J w A)) 0 z := by
  let E := finiteLindbladEvolutionContinuous hamiltonian J
  let G := asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)
  have hE : HasDerivAt E (G * E z) z := by
    exact hasDerivAt_exp_smul_const'
      (asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) z
  have hEA : HasDerivAt (fun w => E w A) ((G * E z) A) z := by
    simpa using hE.clm_apply (hasDerivAt_const z A)
  have htrace := (hasDerivAt_const z continuousOperatorTrace).clm_apply hEA
  have hzero : continuousOperatorTrace ((G * E z) A) = 0 := by
    change continuousOperatorTrace (G (E z A)) = 0
    exact continuousOperatorTrace_generator_eq_zero hamiltonian J (E z A)
  simp only [zero_apply, zero_add, hzero] at htrace
  exact htrace
theorem continuousOperatorTrace_evolution [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (A : ContinuousOperator H) (z : Complex) :
    continuousOperatorTrace
      (finiteLindbladEvolutionContinuous hamiltonian J z A) =
        continuousOperatorTrace A := by
  let f : Complex → Complex := fun w => continuousOperatorTrace
    (finiteLindbladEvolutionContinuous hamiltonian J w A)
  have hf : Differentiable Complex f := fun w =>
    (hasDerivAt_trace_finiteLindbladEvolutionContinuous hamiltonian J A w).differentiableAt
  have hf' : ∀ w, deriv f w = 0 := fun w =>
    (hasDerivAt_trace_finiteLindbladEvolutionContinuous hamiltonian J A w).deriv
  have hconst := is_const_of_deriv_eq_zero hf hf' z 0
  simpa [f] using hconst
theorem finiteLindbladEvolutionLinearMap_trace [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (t : Real)
    (A : Operator H) :
    LinearMap.trace Complex H
      (finiteLindbladEvolutionLinearMap hamiltonian J t A) =
        LinearMap.trace Complex H A := by
  exact continuousOperatorTrace_evolution hamiltonian J
    (LinearMap.toContinuousLinearMap A) (t : Complex)
noncomputable def finiteLindbladEvolutionChannel [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (hhamiltonian : hamiltonian.IsSymmetric)
    (t : Real) (ht : 0 ≤ t) : QuantumChannel H H where
  toLinearMap := finiteLindbladEvolutionLinearMap hamiltonian J t
  completely_positive :=
    finiteLindbladEvolutionLinearMap_completelyPositive
      hamiltonian J hhamiltonian t ht
  trace_preserving := finiteLindbladEvolutionLinearMap_trace hamiltonian J t
end
end QEC.Semantics



-- Prove2me | Definitions.Def_QEC_Semantics_Channels_Kraus
-- name    : QEC_Semantics_Channels_Kraus
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:08:27.123399+00:00
-- url     : https://prove2.me/theorems/67d75aad-41ab-4c76-b386-912a123b1641
-- title:
--   Kraus
-- statement:
--   Definitions and structural lemmas for Kraus, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean

import Definitions.Def_QEC_Semantics_Channels_Core
import Theorems.Thm_QEC_Semantics_Correctable_unitaryTransport
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_symm_conjDensity_transport_iff
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
universe u v
namespace QEC
namespace Semantics
open scoped BigOperators
noncomputable section
abbrev KrausOperator (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    Type u :=
  H →ₗ[Complex] K
structure FiniteKrausFamily (ι : Type v) [Fintype ι] (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] where
  operator : ι → KrausOperator H K
section TracePairing
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
end TracePairing
namespace FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
def Complete (E : FiniteKrausFamily ι H K) : Prop :=
  ∑ i : ι, (LinearMap.adjoint (E.operator i)).comp (E.operator i) = 1
noncomputable def scale (E : FiniteKrausFamily ι H K) (amp : ι → Complex) :
    FiniteKrausFamily ι H K where
  operator i := amp i • E.operator i
@[simp]
theorem scale_operator (E : FiniteKrausFamily ι H K) (amp : ι → Complex) (i : ι) :
    (E.scale amp).operator i = amp i • E.operator i :=
  rfl
def inducedMap (E : FiniteKrausFamily ι H K) :
    Operator H →ₗ[Complex] Operator K where
  toFun A := ∑ i : ι, (E.operator i).comp (A.comp (LinearMap.adjoint (E.operator i)))
  map_add' := by
    intro A B
    ext x
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro c A
    ext x
    simp [Finset.smul_sum]
@[simp]
theorem inducedMap_apply (E : FiniteKrausFamily ι H K) (A : Operator H) :
    E.inducedMap A =
      ∑ i : ι, (E.operator i).comp (A.comp (LinearMap.adjoint (E.operator i))) :=
  rfl
theorem inducedMap_completelyPositive (E : FiniteKrausFamily ι H K) :
    CompletelyPositive E.inducedMap := by
  classical
  intro n M hM
  constructor
  · intro i j
    ext x
    simp [OperatorMatrix.map, inducedMap_apply, hM.1 i j, LinearMap.adjoint_comp]
  · intro x
    have hQuadratic :
        Complex.re (∑ i : Fin n, ∑ j : Fin n,
          inner Complex ((OperatorMatrix.map E.inducedMap M) i j (x j)) (x i)) =
        ∑ a : ι, Complex.re
          (∑ i : Fin n, ∑ j : Fin n,
            inner Complex (M i j ((LinearMap.adjoint (E.operator a)) (x j)))
              ((LinearMap.adjoint (E.operator a)) (x i))) := by
      calc
        Complex.re (∑ i : Fin n, ∑ j : Fin n,
            inner Complex ((OperatorMatrix.map E.inducedMap M) i j (x j)) (x i))
            = Complex.re (∑ i : Fin n, ∑ j : Fin n, ∑ a : ι,
                inner Complex ((E.operator a)
                  (M i j ((LinearMap.adjoint (E.operator a)) (x j)))) (x i)) := by
              simp only [OperatorMatrix.map, inducedMap_apply, LinearMap.sum_apply,
                LinearMap.comp_apply, sum_inner]
        _ = Complex.re (∑ i : Fin n, ∑ j : Fin n, ∑ a : ι,
                inner Complex (M i j ((LinearMap.adjoint (E.operator a)) (x j)))
                  ((LinearMap.adjoint (E.operator a)) (x i))) := by
              congr 1
              apply Finset.sum_congr rfl
              intro i _hi
              apply Finset.sum_congr rfl
              intro j _hj
              apply Finset.sum_congr rfl
              intro a _ha
              exact (LinearMap.adjoint_inner_right (𝕜 := Complex) (E.operator a)
                (M i j ((LinearMap.adjoint (E.operator a)) (x j))) (x i)).symm
        _ = Complex.re (∑ a : ι, ∑ i : Fin n, ∑ j : Fin n,
                inner Complex (M i j ((LinearMap.adjoint (E.operator a)) (x j)))
                  ((LinearMap.adjoint (E.operator a)) (x i))) := by
              congr 1
              calc
                (∑ i : Fin n, ∑ j : Fin n, ∑ a : ι,
                  inner Complex (M i j ((LinearMap.adjoint (E.operator a)) (x j)))
                    ((LinearMap.adjoint (E.operator a)) (x i)))
                    = ∑ i : Fin n, ∑ a : ι, ∑ j : Fin n,
                  inner Complex (M i j ((LinearMap.adjoint (E.operator a)) (x j)))
                    ((LinearMap.adjoint (E.operator a)) (x i)) := by
                      apply Finset.sum_congr rfl
                      intro i _hi
                      rw [Finset.sum_comm]
                _ = ∑ a : ι, ∑ i : Fin n, ∑ j : Fin n,
                  inner Complex (M i j ((LinearMap.adjoint (E.operator a)) (x j)))
                    ((LinearMap.adjoint (E.operator a)) (x i)) := by
                      rw [Finset.sum_comm]
        _ = ∑ a : ι, Complex.re
          (∑ i : Fin n, ∑ j : Fin n,
            inner Complex (M i j ((LinearMap.adjoint (E.operator a)) (x j)))
              ((LinearMap.adjoint (E.operator a)) (x i))) := by
              rw [Complex.re_sum]
    rw [hQuadratic]
    exact Finset.sum_nonneg (by
      intro a _ha
      exact hM.2 (fun i : Fin n => (LinearMap.adjoint (E.operator a)) (x i)))
theorem inducedMap_trace_eq_trace_comp_completeSum (E : FiniteKrausFamily ι H K)
    (A : Operator H) :
    LinearMap.trace Complex K (E.inducedMap A) =
      LinearMap.trace Complex H
        (A.comp (∑ i : ι, (LinearMap.adjoint (E.operator i)).comp (E.operator i))) := by
  classical
  unfold inducedMap
  calc
    LinearMap.trace Complex K
        (∑ i : ι, (E.operator i).comp (A.comp (LinearMap.adjoint (E.operator i))))
        = ∑ i : ι, LinearMap.trace Complex K
            ((E.operator i).comp (A.comp (LinearMap.adjoint (E.operator i)))) := by
          rw [map_sum]
    _ = ∑ i : ι, LinearMap.trace Complex H
            (A.comp ((LinearMap.adjoint (E.operator i)).comp (E.operator i))) := by
          apply Finset.sum_congr rfl
          intro i _hi
          simpa [LinearMap.comp_assoc] using
            (LinearMap.trace_comp_cycle
              (R := Complex) (M := H) (N := H) (P := K)
              (f := A) (g := E.operator i) (h := LinearMap.adjoint (E.operator i)))
    _ = LinearMap.trace Complex H
        (∑ i : ι, A.comp ((LinearMap.adjoint (E.operator i)).comp (E.operator i))) := by
          rw [map_sum]
    _ = LinearMap.trace Complex H
        (A.comp (∑ i : ι, (LinearMap.adjoint (E.operator i)).comp (E.operator i))) := by
          congr 1
          ext x
          simp [Finset.sum_apply]
theorem inducedMap_trace_preserving (E : FiniteKrausFamily ι H K)
    (hE : E.Complete) (A : Operator H) :
    LinearMap.trace Complex K (E.inducedMap A) = LinearMap.trace Complex H A := by
  classical
  calc
    LinearMap.trace Complex K (E.inducedMap A)
        = LinearMap.trace Complex H
            (A.comp (∑ i : ι, (LinearMap.adjoint (E.operator i)).comp (E.operator i))) :=
          E.inducedMap_trace_eq_trace_comp_completeSum A
    _ = LinearMap.trace Complex H A := by
          rw [hE]
          rfl
noncomputable def toQuantumChannel (E : FiniteKrausFamily ι H K) (hE : E.Complete) :
    QuantumChannel H K where
  toLinearMap := E.inducedMap
  completely_positive := E.inducedMap_completelyPositive
  trace_preserving := E.inducedMap_trace_preserving hE
@[simp]
theorem toQuantumChannel_toLinearMap (E : FiniteKrausFamily ι H K) (hE : E.Complete) :
    (E.toQuantumChannel hE).toLinearMap = E.inducedMap :=
  rfl
@[simp]
theorem toQuantumChannel_apply (E : FiniteKrausFamily ι H K) (hE : E.Complete)
    (A : Operator H) :
    (E.toQuantumChannel hE) A = E.inducedMap A :=
  rfl
noncomputable def unitaryTransport (E : FiniteKrausFamily ι H K)
    {Ht Kt : Type u}
    [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
    [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt) :
    FiniteKrausFamily ι Ht Kt where
  operator i := V.toLinearEquiv.toLinearMap.comp
    ((E.operator i).comp U.toLinearEquiv.symm.toLinearMap)
@[simp]
theorem unitaryTransport_operator (E : FiniteKrausFamily ι H K)
    {Ht Kt : Type u}
    [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
    [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt) (i : ι) :
    (E.unitaryTransport U V).operator i =
      V.toLinearEquiv.toLinearMap.comp
        ((E.operator i).comp U.toLinearEquiv.symm.toLinearMap) :=
  rfl
theorem unitaryTransport_complete (E : FiniteKrausFamily ι H K)
    {Ht Kt : Type u}
    [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
    [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    (hE : E.Complete) :
    (E.unitaryTransport U V).Complete := by
  classical
  unfold Complete unitaryTransport
  ext x
  have hEx := congrArg (fun A : Operator H => A (U.toLinearEquiv.symm x)) hE
  have hEx' :
      (∑ i : ι, (LinearMap.adjoint (E.operator i))
        ((E.operator i) (U.toLinearEquiv.symm x))) = U.toLinearEquiv.symm x := by
    simpa [Finset.sum_apply, LinearMap.comp_apply] using hEx
  simp [U.adjoint_symm_toLinearMap, V.adjoint_toLinearMap]
  calc
    ∑ i : ι, U.toLinearEquiv
        ((LinearMap.adjoint (E.operator i))
          ((E.operator i) (U.toLinearEquiv.symm x))) =
        U.toLinearEquiv (∑ i : ι,
          (LinearMap.adjoint (E.operator i))
            ((E.operator i) (U.toLinearEquiv.symm x))) := by
          simp
    _ = x := by
          rw [hEx']
          simp
theorem unitaryTransport_inducedMap_apply (E : FiniteKrausFamily ι H K)
    {Ht Kt : Type u}
    [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
    [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    (A : Operator Ht) :
    (E.unitaryTransport U V).inducedMap A =
      V.conjOperator (E.inducedMap (U.symm.conjOperator A)) := by
  ext x
  simp [unitaryTransport, inducedMap_apply, UnitaryTransport.conjOperator,
    UnitaryTransport.symm, U.adjoint_symm_toLinearMap, V.adjoint_toLinearMap,
    Finset.sum_apply]
@[simp]
theorem unitaryTransport_symm_operator (E : FiniteKrausFamily ι H K)
    {Ht Kt : Type u}
    [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
    [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt) (i : ι) :
    ((E.unitaryTransport U V).unitaryTransport U.symm V.symm).operator i =
      E.operator i := by
  ext x
  simp [unitaryTransport, UnitaryTransport.symm]
def sameSpaceErrorSet (E : FiniteKrausFamily ι H H) : Set (Operator H) :=
  Set.range E.operator
def sameSpaceKnillLaflammeCriterion
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) : Prop :=
  KnillLaflammeCriterion H C E.sameSpaceErrorSet
def CorrectedBy (E : FiniteKrausFamily ι H K)
    (C : QuantumCode H) (recovery : QuantumChannel K H) : Prop :=
  ∀ rho : DensityOperator H,
    DensityOperator.SupportedOn C rho →
      recovery (E.inducedMap rho.toOperator) = rho.toOperator
end FiniteKrausFamily
def FiniteKrausCorrectable (ι : Type v) [Fintype ι] (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (C : QuantumCode H) (noise : FiniteKrausFamily ι H K)
    (recovery : QuantumChannel K H) : Prop :=
  noise.Complete ∧ noise.CorrectedBy C recovery
namespace FiniteKrausCorrectable
variable {ι : Type v} [Fintype ι]
variable {H K Ht Kt : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
variable [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]
theorem unitaryTransport
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    {C : QuantumCode H} {noise : FiniteKrausFamily ι H K}
    {recovery : QuantumChannel K H}
    (h : FiniteKrausCorrectable ι H K C noise recovery) :
    FiniteKrausCorrectable ι Ht Kt (C.transport U)
      (noise.unitaryTransport U V)
      (QuantumChannel.comp (QuantumChannel.unitaryConj U)
        (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V.symm))) := by
  rcases h with ⟨hcomplete, hcorrected⟩
  constructor
  · exact noise.unitaryTransport_complete U V hcomplete
  · intro rho hρ
    let rho₀ : DensityOperator H := U.symm.conjDensity rho
    have hρ₀ : DensityOperator.SupportedOn C rho₀ := by
      exact (DensityOperator.supportedOn_symm_conjDensity_transport_iff U C rho).2 hρ
    have hcorr := hcorrected rho₀ hρ₀
    have hcorr' : recovery (noise.inducedMap (U.symm.conjOperator rho.toOperator)) =
        U.symm.conjOperator rho.toOperator := by
      simpa [rho₀] using hcorr
    change U.conjOperator
        (recovery (V.symm.conjOperator
          ((noise.unitaryTransport U V).inducedMap rho.toOperator))) = rho.toOperator
    rw [FiniteKrausFamily.unitaryTransport_inducedMap_apply]
    rw [UnitaryTransport.symm_conjOperator_conjOperator]
    rw [hcorr']
    rw [UnitaryTransport.conjOperator_symm_conjOperator]
end FiniteKrausCorrectable
end
end Semantics
end QEC



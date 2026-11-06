-- Prove2me | Definitions.Def_QEC_Semantics_Channels_Core
-- name    : QEC_Semantics_Channels_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:42:01.517422+00:00
-- url     : https://prove2.me/theorems/dcb170fb-9e00-48b5-96a6-056f777bd3aa
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Core.lean

import Definitions.Def_QEC_Semantics_Core_Definitions
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_completely_positive
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_trace_preserving
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
universe u
namespace QEC
namespace Semantics
open scoped TensorProduct
namespace OperatorMatrix
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
def oneByOne (A : Operator H) : OperatorMatrix 1 H :=
  fun _ _ => A
@[simp]
theorem oneByOne_apply (A : Operator H) (i j : Fin 1) :
    oneByOne A i j = A :=
  rfl
theorem oneByOne_isPositive_iff (A : Operator H) :
    IsPositive (oneByOne A) ↔ LinearMap.IsPositive A := by
  constructor
  · intro hM
    constructor
    · have hAdj : A = LinearMap.adjoint A := by
        simpa [oneByOne] using hM.1 0 0
      intro x y
      calc
        inner Complex (A x) y = inner Complex ((LinearMap.adjoint A) x) y := by
          exact congrArg (fun T : Operator H => inner Complex (T x) y) hAdj
        _ = inner Complex x (A y) := by
          simpa using (LinearMap.adjoint_inner_left (𝕜 := Complex) A y x)
    · intro x
      simpa [oneByOne] using hM.2 (fun _ : Fin 1 => x)
  · intro hA
    constructor
    · intro i j
      fin_cases i
      fin_cases j
      simpa [oneByOne] using hA.1.adjoint_eq.symm
    · intro x
      simpa [oneByOne] using hA.2 (x 0)
end OperatorMatrix
namespace CompletelyPositive
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
theorem map_positive {Φ : Operator H →ₗ[Complex] Operator K}
    (hΦ : CompletelyPositive Φ) {A : Operator H}
    (hA : LinearMap.IsPositive A) : LinearMap.IsPositive (Φ A) := by
  have hBlock :
      OperatorMatrix.IsPositive
        (OperatorMatrix.map Φ (OperatorMatrix.oneByOne A)) :=
    hΦ 1 (OperatorMatrix.oneByOne A)
      ((OperatorMatrix.oneByOne_isPositive_iff A).2 hA)
  have hmap : OperatorMatrix.map Φ (OperatorMatrix.oneByOne A) =
      OperatorMatrix.oneByOne (Φ A) := by
    ext i j
    rfl
  rw [hmap] at hBlock
  exact (OperatorMatrix.oneByOne_isPositive_iff (Φ A)).1 hBlock
end CompletelyPositive
namespace UnitaryTransport
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
noncomputable def conjOperatorLinearMap (U : UnitaryTransport H K) :
    Operator H →ₗ[Complex] Operator K where
  toFun := U.conjOperator
  map_add' := by
    intro A B
    ext x
    simp [UnitaryTransport.conjOperator]
  map_smul' := by
    intro c A
    ext x
    simp [UnitaryTransport.conjOperator]
@[simp]
theorem conjOperatorLinearMap_apply (U : UnitaryTransport H K) (A : Operator H) :
    U.conjOperatorLinearMap A = U.conjOperator A :=
  rfl
@[simp]
theorem inner_conjOperator (U : UnitaryTransport H K) (A : Operator H) (x y : K) :
    inner Complex ((U.conjOperator A) x) y =
      inner Complex (A (U.toLinearEquiv.symm x)) (U.toLinearEquiv.symm y) := by
  rw [UnitaryTransport.conjOperator_apply]
  nth_rewrite 1 [← U.toLinearEquiv.apply_symm_apply y]
  exact U.map_inner (A (U.toLinearEquiv.symm x)) (U.toLinearEquiv.symm y)
theorem completelyPositive_conjOperator (U : UnitaryTransport H K) :
    CompletelyPositive U.conjOperatorLinearMap := by
  intro n M hM
  constructor
  · intro i j
    change U.conjOperator (M j i) = LinearMap.adjoint (U.conjOperator (M i j))
    rw [hM.1 i j, UnitaryTransport.conjOperator_adjoint]
  · intro x
    have hPullback := hM.2 (fun i : Fin n => U.toLinearEquiv.symm (x i))
    simpa only [OperatorMatrix.map, conjOperatorLinearMap_apply, inner_conjOperator] using hPullback
end UnitaryTransport
namespace QuantumChannel
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
theorem map_positive (Φ : QuantumChannel H K) {A : Operator H}
    (hA : LinearMap.IsPositive A) : LinearMap.IsPositive (Φ A) :=
  Φ.completely_positive.map_positive hA
noncomputable def mapDensity (Φ : QuantumChannel H K)
    (rho : DensityOperator H) : DensityOperator K where
  toOperator := Φ rho.toOperator
  positive := Φ.map_positive rho.positive
  trace_one := by
    rw [Φ.trace_map, rho.trace_one]
@[simp]
theorem mapDensity_toOperator (Φ : QuantumChannel H K)
    (rho : DensityOperator H) :
    (Φ.mapDensity rho).toOperator = Φ rho.toOperator :=
  rfl
noncomputable def unitaryConj (U : UnitaryTransport H K) : QuantumChannel H K where
  toLinearMap := U.conjOperatorLinearMap
  completely_positive := U.completelyPositive_conjOperator
  trace_preserving := by
    intro A
    simpa [UnitaryTransport.conjOperatorLinearMap_apply] using
      (UnitaryTransport.trace_conjOperator U A)
@[simp]
theorem unitaryConj_apply (U : UnitaryTransport H K) (A : Operator H) :
    (unitaryConj U) A = U.conjOperator A :=
  rfl
noncomputable def id (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] : QuantumChannel H H where
  toLinearMap := LinearMap.id
  completely_positive := by
    intro n M hM
    have hmap : OperatorMatrix.map (LinearMap.id : Operator H →ₗ[Complex] Operator H) M =
        M := by
      ext i j
      rfl
    rw [hmap]
    exact hM
  trace_preserving := by
    intro A
    rfl
noncomputable def comp {L : Type u} [NormedAddCommGroup L] [InnerProductSpace Complex L]
    [FiniteQuantumSystem L] (Ψ : QuantumChannel K L) (Φ : QuantumChannel H K) :
    QuantumChannel H L where
  toLinearMap := Ψ.toLinearMap.comp Φ.toLinearMap
  completely_positive := by
    intro n M hM
    exact Ψ.completely_positive n (OperatorMatrix.map Φ.toLinearMap M)
      (Φ.completely_positive n M hM)
  trace_preserving := by
    intro A
    calc
      LinearMap.trace Complex L ((Ψ.toLinearMap.comp Φ.toLinearMap) A)
          = LinearMap.trace Complex K (Φ.toLinearMap A) := Ψ.trace_map (Φ.toLinearMap A)
      _ = LinearMap.trace Complex H A := Φ.trace_map A
end QuantumChannel
namespace Correctable
variable {H K Ht Kt : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
variable [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]
end Correctable
noncomputable def partialTraceRightRaw_cptp (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    QuantumChannel (CompositeSystem H K) H where
  toLinearMap := partialTraceRightRaw H K
  completely_positive := partialTraceRightRaw_completely_positive H K
  trace_preserving := partialTraceRightRaw_trace_preserving H K
noncomputable def partialTraceRightRaw_mapDensity (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator (CompositeSystem H K)) : DensityOperator H :=
  (partialTraceRightRaw_cptp H K).mapDensity rho
end Semantics
end QEC



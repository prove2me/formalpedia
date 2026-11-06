-- Prove2me | Definitions.Def_QEC_Semantics_Core_Definitions
-- name    : QEC_Semantics_Core_Definitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:52:59.215678+00:00
-- url     : https://prove2.me/theorems/6d0b159a-9afc-4c30-853a-f8be1fbc07d7
-- title:
--   Definitions
-- statement:
--   Definitions and structural lemmas for Definitions, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean

import Mathlib
set_option autoImplicit false
universe u
namespace QEC
namespace Semantics
open scoped TensorProduct ComplexOrder
abbrev FiniteQuantumSystem (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] : Prop :=
  FiniteDimensional Complex H
abbrev Operator (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] : Type u :=
  Module.End Complex H
example (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] : Operator H = Module.End Complex H := rfl
noncomputable example {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (A : Operator H) : Complex :=
  LinearMap.trace Complex H A
example {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (A : Operator H) : Prop :=
  LinearMap.IsPositive A
structure DensityOperator (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] where
  toOperator : Operator H
  positive : LinearMap.IsPositive toOperator
  trace_one : LinearMap.trace Complex H toOperator = 1
namespace DensityOperator
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
instance : Coe (DensityOperator H) (Operator H) where
  coe rho := rho.toOperator
example : DensityOperator H → Operator H := fun rho => rho
end DensityOperator
structure PositiveTracePreservingMap (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] where
  toPositiveMap : Operator H →ₚ[Complex] Operator K
  trace_preserving : ∀ A : Operator H,
    LinearMap.trace Complex K (toPositiveMap A) = LinearMap.trace Complex H A
namespace PositiveTracePreservingMap
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
noncomputable instance : CoeFun (PositiveTracePreservingMap H K)
    (fun _ => Operator H → Operator K) where
  coe Φ := Φ.toPositiveMap
theorem trace_map (Φ : PositiveTracePreservingMap H K) (A : Operator H) :
    LinearMap.trace Complex K (Φ A) = LinearMap.trace Complex H A :=
  Φ.trace_preserving A
theorem map_positive (Φ : PositiveTracePreservingMap H K) {A : Operator H}
    (hA : LinearMap.IsPositive A) : LinearMap.IsPositive (Φ A) := by
  rw [← LinearMap.nonneg_iff_isPositive] at hA ⊢
  exact PositiveLinearMap.map_nonneg Φ.toPositiveMap hA
noncomputable example {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] : PositiveTracePreservingMap H K → Operator H → Operator K :=
  fun Φ => Φ
end PositiveTracePreservingMap
abbrev OperatorMatrix (n : Nat) (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] : Type u :=
  Matrix (Fin n) (Fin n) (Operator H)
namespace OperatorMatrix
variable {n : Nat} {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
def IsPositive (M : OperatorMatrix n H) : Prop :=
  (∀ i j : Fin n, M j i = LinearMap.adjoint (M i j)) ∧
    ∀ x : Fin n → H,
      0 ≤ Complex.re (∑ i : Fin n, ∑ j : Fin n, inner Complex (M i j (x j)) (x i))
noncomputable abbrev scalarMatrix {β : Type*} [Fintype β]
    (M : OperatorMatrix n H) (b : OrthonormalBasis β Complex H) :
    Matrix (Fin n × β) (Fin n × β) Complex :=
  fun ip jq => inner Complex (M ip.1 jq.1 (b jq.2)) (b ip.2)
def map (Φ : Operator H →ₗ[Complex] Operator K) (M : OperatorMatrix n H) :
    OperatorMatrix n K :=
  fun i j => Φ (M i j)
end OperatorMatrix
def CompletelyPositive {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Φ : Operator H →ₗ[Complex] Operator K) : Prop :=
  ∀ (n : Nat) (M : OperatorMatrix n H),
    OperatorMatrix.IsPositive M → OperatorMatrix.IsPositive (OperatorMatrix.map Φ M)
structure QuantumChannel (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] where
  toLinearMap : Operator H →ₗ[Complex] Operator K
  completely_positive : CompletelyPositive toLinearMap
  trace_preserving : ∀ A : Operator H,
    LinearMap.trace Complex K (toLinearMap A) = LinearMap.trace Complex H A
namespace QuantumChannel
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
noncomputable instance : CoeFun (QuantumChannel H K)
    (fun _ => Operator H → Operator K) where
  coe Φ := Φ.toLinearMap
theorem trace_map (Φ : QuantumChannel H K) (A : Operator H) :
    LinearMap.trace Complex K (Φ A) = LinearMap.trace Complex H A :=
  Φ.trace_preserving A
noncomputable example {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] : QuantumChannel H K → Operator H → Operator K :=
  fun Φ => Φ
end QuantumChannel
abbrev CompositeSystem (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] : Type u :=
  H ⊗[Complex] K
noncomputable def partialTraceRightRaw (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    Operator (CompositeSystem H K) →ₗ[Complex] Operator H :=
  let unwrap :
      Operator (CompositeSystem H K) →ₗ[Complex]
        Module.Dual Complex (CompositeSystem H K) ⊗[Complex] CompositeSystem H K :=
    (dualTensorHomEquiv Complex (CompositeSystem H K) (CompositeSystem H K)).symm.toLinearMap
  let splitDual :
      Module.Dual Complex (CompositeSystem H K) →ₗ[Complex]
        Module.Dual Complex H ⊗[Complex] Module.Dual Complex K :=
    (TensorProduct.dualDistribEquiv Complex H K).symm.toLinearMap
  let split :
      Module.Dual Complex (CompositeSystem H K) ⊗[Complex] CompositeSystem H K →ₗ[Complex]
        (Module.Dual Complex H ⊗[Complex] Module.Dual Complex K) ⊗[Complex]
          (H ⊗[Complex] K) :=
    TensorProduct.map splitDual
      (LinearMap.id : CompositeSystem H K →ₗ[Complex] CompositeSystem H K)
  let commute :
      (Module.Dual Complex H ⊗[Complex] Module.Dual Complex K) ⊗[Complex]
          (H ⊗[Complex] K) →ₗ[Complex]
        (Module.Dual Complex H ⊗[Complex] H) ⊗[Complex]
          (Module.Dual Complex K ⊗[Complex] K) :=
    (TensorProduct.tensorTensorTensorComm Complex
      (Module.Dual Complex H) (Module.Dual Complex K) H K).toLinearMap
  let contractK :
      (Module.Dual Complex H ⊗[Complex] H) ⊗[Complex]
          (Module.Dual Complex K ⊗[Complex] K) →ₗ[Complex]
        (Module.Dual Complex H ⊗[Complex] H) ⊗[Complex] Complex :=
    TensorProduct.map
      (LinearMap.id : Module.Dual Complex H ⊗[Complex] H →ₗ[Complex]
        Module.Dual Complex H ⊗[Complex] H)
      (contractLeft Complex K)
  let dropScalar :
      (Module.Dual Complex H ⊗[Complex] H) ⊗[Complex] Complex →ₗ[Complex]
        Module.Dual Complex H ⊗[Complex] H :=
    (TensorProduct.rid Complex (Module.Dual Complex H ⊗[Complex] H)).toLinearMap
  let rewrap : Module.Dual Complex H ⊗[Complex] H →ₗ[Complex] Operator H :=
    (dualTensorHomEquiv Complex H H).toLinearMap
  rewrap.comp (dropScalar.comp (contractK.comp (commute.comp (split.comp unwrap))))
noncomputable def tensorRight (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (k : K) : H →ₗ[Complex] CompositeSystem H K :=
  (TensorProduct.mk Complex H K).flip k
noncomputable def partialTraceRightCompression (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    Operator (CompositeSystem H K) →ₗ[Complex] Operator H :=
  let bK := stdOrthonormalBasis Complex K
  ∑ i : Fin (Module.finrank Complex K),
    let S := tensorRight H K (bK i)
    { toFun := fun A => (LinearMap.adjoint S).comp (A.comp S)
      map_add' := by
        intro A B
        ext x
        simp [LinearMap.comp_apply, map_add]
      map_smul' := by
        intro c A
        ext x
        simp [LinearMap.comp_apply] }
structure PartialTraceRight (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] where
  toMap : Operator (CompositeSystem H K) →ₗ[Complex] Operator H
  map_positive : ∀ {A : Operator (CompositeSystem H K)},
    LinearMap.IsPositive A → LinearMap.IsPositive (toMap A)
  trace_preserving : ∀ A : Operator (CompositeSystem H K),
    LinearMap.trace Complex H (toMap A) = LinearMap.trace Complex (CompositeSystem H K) A
namespace PartialTraceRight
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
noncomputable instance : CoeFun (PartialTraceRight H K)
    (fun _ => Operator (CompositeSystem H K) → Operator H) where
  coe tr := tr.toMap
theorem trace_map (tr : PartialTraceRight H K) (A : Operator (CompositeSystem H K)) :
    LinearMap.trace Complex H (tr A) = LinearMap.trace Complex (CompositeSystem H K) A :=
  tr.trace_preserving A
noncomputable def mapDensity (tr : PartialTraceRight H K)
    (rho : DensityOperator (CompositeSystem H K)) : DensityOperator H where
  toOperator := tr rho.toOperator
  positive := tr.map_positive rho.positive
  trace_one := by
    rw [tr.trace_map, rho.trace_one]
end PartialTraceRight
structure QuantumCode (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] where
  carrier : Submodule Complex H
namespace QuantumCode
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
instance : Coe (QuantumCode H) (Submodule Complex H) where
  coe C := C.carrier
noncomputable def dimension (C : QuantumCode H) : Nat :=
  Module.finrank Complex C.carrier
@[simp]
theorem dimension_eq_finrank_carrier (C : QuantumCode H) :
    C.dimension = Module.finrank Complex C.carrier :=
  rfl
end QuantumCode
namespace DensityOperator
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
def SupportedOn (C : QuantumCode H) (rho : DensityOperator H) : Prop :=
  ∀ v : H, rho.toOperator v ∈ C.carrier
end DensityOperator
def Correctable (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (C : QuantumCode H) (noise : QuantumChannel H K)
    (recovery : QuantumChannel K H) : Prop :=
  ∀ rho : DensityOperator H,
    DensityOperator.SupportedOn C rho →
      recovery (noise rho.toOperator) = rho.toOperator
def KnillLaflammeCriterion (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (errors : Set (Operator H)) : Prop :=
  ∃ scalar : Operator H → Operator H → Complex,
    ∀ ⦃E : Operator H⦄, E ∈ errors →
      ∀ ⦃F : Operator H⦄, F ∈ errors →
        ∀ x : H, x ∈ C.carrier →
          ∀ y : H, y ∈ C.carrier →
            inner Complex (E x) (F y) = scalar E F * inner Complex x y
structure UnitaryTransport (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] where
  toLinearEquiv : H ≃ₗ[Complex] K
  map_inner : ∀ x y : H,
    inner Complex (toLinearEquiv x) (toLinearEquiv y) = inner Complex x y
namespace UnitaryTransport
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
instance : CoeFun (UnitaryTransport H K) (fun _ => H → K) where
  coe U := U.toLinearEquiv
noncomputable def symm (U : UnitaryTransport H K) : UnitaryTransport K H where
  toLinearEquiv := U.toLinearEquiv.symm
  map_inner := by
    intro x y
    simpa using (U.map_inner (U.toLinearEquiv.symm x) (U.toLinearEquiv.symm y)).symm
@[simp]
theorem symm_toLinearEquiv (U : UnitaryTransport H K) :
    U.symm.toLinearEquiv = U.toLinearEquiv.symm :=
  rfl
noncomputable def conjOperator (U : UnitaryTransport H K) (A : Operator H) : Operator K :=
  U.toLinearEquiv.toLinearMap.comp (A.comp U.toLinearEquiv.symm.toLinearMap)
noncomputable def toLinearIsometryEquiv (U : UnitaryTransport H K) : H ≃ₗᵢ[Complex] K :=
  U.toLinearEquiv.isometryOfInner U.map_inner
@[simp]
theorem toLinearIsometryEquiv_toLinearEquiv (U : UnitaryTransport H K) :
    U.toLinearIsometryEquiv.toLinearEquiv = U.toLinearEquiv :=
  rfl
@[simp]
theorem toLinearIsometryEquiv_toLinearMap (U : UnitaryTransport H K) :
    U.toLinearIsometryEquiv.toLinearMap = U.toLinearEquiv.toLinearMap :=
  rfl
theorem adjoint_toLinearMap (U : UnitaryTransport H K) :
    LinearMap.adjoint U.toLinearEquiv.toLinearMap = U.toLinearEquiv.symm.toLinearMap := by
  simpa [toLinearIsometryEquiv] using
    (LinearIsometryEquiv.adjoint_toLinearMap_eq_symm U.toLinearIsometryEquiv)
theorem adjoint_symm_toLinearMap (U : UnitaryTransport H K) :
    LinearMap.adjoint U.toLinearEquiv.symm.toLinearMap = U.toLinearEquiv.toLinearMap := by
  simpa [toLinearIsometryEquiv, LinearIsometryEquiv.toLinearEquiv_symm] using
    (LinearIsometryEquiv.adjoint_toLinearMap_eq_symm U.toLinearIsometryEquiv.symm)
theorem conjOperator_eq_linearEquiv_conj (U : UnitaryTransport H K) (A : Operator H) :
    U.conjOperator A = U.toLinearEquiv.conj A :=
  rfl
@[simp]
theorem conjOperator_apply (U : UnitaryTransport H K) (A : Operator H) (x : K) :
    U.conjOperator A x = U.toLinearEquiv (A (U.toLinearEquiv.symm x)) :=
  rfl
@[simp]
theorem symm_conjOperator_conjOperator (U : UnitaryTransport H K) (A : Operator H) :
    U.symm.conjOperator (U.conjOperator A) = A := by
  ext x
  simp [symm, conjOperator]
@[simp]
theorem conjOperator_symm_conjOperator (U : UnitaryTransport H K) (A : Operator K) :
    U.conjOperator (U.symm.conjOperator A) = A := by
  ext x
  simp [symm, conjOperator]
@[simp]
theorem conjOperator_one (U : UnitaryTransport H K) :
    U.conjOperator (1 : Operator H) = (1 : Operator K) := by
  ext x
  simp [conjOperator]
@[simp]
theorem conjOperator_mul (U : UnitaryTransport H K) (A B : Operator H) :
    U.conjOperator (A * B) = U.conjOperator A * U.conjOperator B := by
  ext x
  simp [conjOperator, Module.End.mul_eq_comp]
@[simp]
theorem conjOperator_adjoint (U : UnitaryTransport H K) (A : Operator H) :
    LinearMap.adjoint (U.conjOperator A) = U.conjOperator (LinearMap.adjoint A) := by
  ext x
  simp [conjOperator, U.adjoint_toLinearMap, U.adjoint_symm_toLinearMap]
theorem trace_conjOperator (U : UnitaryTransport H K) (A : Operator H) :
    LinearMap.trace Complex K (U.conjOperator A) = LinearMap.trace Complex H A := by
  simp [conjOperator_eq_linearEquiv_conj]
theorem isPositive_conjOperator (U : UnitaryTransport H K) {A : Operator H}
    (hA : LinearMap.IsPositive A) :
    LinearMap.IsPositive (U.conjOperator A) := by
  have h := (LinearMap.isPositive_linearIsometryEquiv_conj_iff
    (T := A) U.toLinearIsometryEquiv).2 hA
  simpa [conjOperator, toLinearIsometryEquiv] using h
noncomputable def conjDensity (U : UnitaryTransport H K)
    (rho : DensityOperator H) : DensityOperator K where
  toOperator := U.conjOperator rho.toOperator
  positive := U.isPositive_conjOperator rho.positive
  trace_one := by
    rw [U.trace_conjOperator, rho.trace_one]
end UnitaryTransport
namespace QuantumCode
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
def TransportedBy (U : UnitaryTransport H K) (C : QuantumCode H) (D : QuantumCode K) :
    Prop :=
  ∀ x : H, x ∈ C.carrier ↔ U x ∈ D.carrier
def transport (U : UnitaryTransport H K) (C : QuantumCode H) : QuantumCode K where
  carrier := C.carrier.map U.toLinearEquiv.toLinearMap
end QuantumCode
namespace DensityOperator
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
end DensityOperator
noncomputable def UnitaryInvariance (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (U : UnitaryTransport H K) (C : QuantumCode H) (D : QuantumCode K)
    (errors : Set (Operator H)) : Prop :=
  QuantumCode.TransportedBy U C D →
    KnillLaflammeCriterion H C errors →
      KnillLaflammeCriterion K D (Set.image (UnitaryTransport.conjOperator U) errors)
end Semantics
end QEC



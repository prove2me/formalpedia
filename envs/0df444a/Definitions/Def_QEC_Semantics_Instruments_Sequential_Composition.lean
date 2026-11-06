-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
-- name    : QEC_Semantics_Instruments_Sequential_Composition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:34:35.657335+00:00
-- url     : https://prove2.me/theorems/3964fedb-8993-4d91-a3ca-bbf648193d28
-- title:
--   Composition
-- statement:
--   Definitions and structural lemmas for Composition, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/Composition.lean

import Definitions.Def_QEC_Semantics_Instruments_Core
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
universe u v w x y
namespace QEC
namespace Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
namespace FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {κ' : Type x} [Fintype κ']
variable {Ξ : Ω → Type y} [∀ outcome, Fintype (Ξ outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
noncomputable def bind (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument κ' (Ξ outcome) K L) :
    FiniteInstrument (κ × κ') (Sigma Ξ) H L where
  kraus :=
    { operator index :=
      ((J (I.observe index.1)).kraus.operator index.2).comp
        (I.kraus.operator index.1) }
  observe := fun index =>
    ⟨I.observe index.1, (J (I.observe index.1)).observe index.2⟩
section Tensor
variable {Ω' : Type y} [Fintype Ω']
variable {R S : Type u}
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]
noncomputable def tensor (I : FiniteInstrument κ Ω H K)
    (J : FiniteInstrument κ' Ω' R S) :
    FiniteInstrument (κ × κ') (Ω × Ω')
      (CompositeSystem H R) (CompositeSystem K S) where
  kraus :=
    { operator index :=
      TensorProduct.map (I.kraus.operator index.1) (J.kraus.operator index.2) }
  observe := fun index => (I.observe index.1, J.observe index.2)
end Tensor
section TensorPower
def tensorPowerHistory (α : Type v) : Nat → Type v
  | 0 => PUnit
  | n + 1 => α × tensorPowerHistory α n
instance tensorPowerHistoryFintype (α : Type v) [Fintype α] (n : Nat) :
    Fintype (tensorPowerHistory α n) := by
  induction n with
  | zero =>
      simpa [tensorPowerHistory] using (inferInstance : Fintype PUnit)
  | succ n ih =>
      simpa [tensorPowerHistory] using
        (inferInstance : Fintype (α × tensorPowerHistory α n))
structure TensorPowerSystem where
  carrier : Type u
  normedAddCommGroup : NormedAddCommGroup carrier
  innerProductSpace : @InnerProductSpace Complex carrier (inferInstance : RCLike Complex)
    normedAddCommGroup.toSeminormedAddCommGroup
  finiteDimensional :
    letI : NormedAddCommGroup carrier := normedAddCommGroup
    letI : InnerProductSpace Complex carrier := innerProductSpace
    FiniteQuantumSystem carrier
noncomputable instance (S : TensorPowerSystem) : NormedAddCommGroup S.carrier :=
  S.normedAddCommGroup
noncomputable instance (S : TensorPowerSystem) : InnerProductSpace Complex S.carrier :=
  S.innerProductSpace
noncomputable instance (S : TensorPowerSystem) : FiniteQuantumSystem S.carrier :=
  S.finiteDimensional
@[reducible] noncomputable def tensorPowerSystemOf (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [FiniteQuantumSystem H] : TensorPowerSystem := by
  let normed : NormedAddCommGroup H := inferInstance
  letI : NormedAddCommGroup H := normed
  let inner : InnerProductSpace Complex H := inferInstance
  letI : InnerProductSpace Complex H := inner
  let finite : FiniteQuantumSystem H := inferInstance
  exact
    { carrier := H
      normedAddCommGroup := normed
      innerProductSpace := inner
      finiteDimensional := finite }
@[reducible] noncomputable def tensorUnitSystem : TensorPowerSystem := by
  let normed : NormedAddCommGroup (EuclideanSpace Complex (ULift.{u} (Fin 1))) :=
    inferInstance
  letI : NormedAddCommGroup (EuclideanSpace Complex (ULift.{u} (Fin 1))) := normed
  let inner : InnerProductSpace Complex (EuclideanSpace Complex (ULift.{u} (Fin 1))) :=
    inferInstance
  letI : InnerProductSpace Complex (EuclideanSpace Complex (ULift.{u} (Fin 1))) := inner
  let finite : FiniteQuantumSystem (EuclideanSpace Complex (ULift.{u} (Fin 1))) :=
    inferInstance
  exact
    { carrier := EuclideanSpace Complex (ULift.{u} (Fin 1))
      normedAddCommGroup := normed
      innerProductSpace := inner
      finiteDimensional := finite }
@[reducible] noncomputable def tensorPowerSystemTensor (S T : TensorPowerSystem) :
    TensorPowerSystem := by
  letI : NormedAddCommGroup S.carrier := S.normedAddCommGroup
  letI : InnerProductSpace Complex S.carrier := S.innerProductSpace
  letI : FiniteQuantumSystem S.carrier := S.finiteDimensional
  letI : NormedAddCommGroup T.carrier := T.normedAddCommGroup
  letI : InnerProductSpace Complex T.carrier := T.innerProductSpace
  letI : FiniteQuantumSystem T.carrier := T.finiteDimensional
  let normed : NormedAddCommGroup (S.carrier ⊗[Complex] T.carrier) := inferInstance
  letI : NormedAddCommGroup (S.carrier ⊗[Complex] T.carrier) := normed
  let inner : InnerProductSpace Complex (S.carrier ⊗[Complex] T.carrier) := inferInstance
  letI : InnerProductSpace Complex (S.carrier ⊗[Complex] T.carrier) := inner
  let finite : FiniteQuantumSystem (S.carrier ⊗[Complex] T.carrier) := inferInstance
  exact
    { carrier := S.carrier ⊗[Complex] T.carrier
      normedAddCommGroup := normed
      innerProductSpace := inner
      finiteDimensional := finite }
@[reducible] noncomputable def tensorPowerSystem (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [FiniteQuantumSystem H] : Nat → TensorPowerSystem
  | 0 => tensorUnitSystem
  | n + 1 => tensorPowerSystemTensor (tensorPowerSystemOf H) (tensorPowerSystem H n)
abbrev tensorPowerCarrier (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [FiniteQuantumSystem H] (n : Nat) : Type u :=
  (tensorPowerSystem H n).carrier
noncomputable def tensorUnitInstrument :
    FiniteInstrument PUnit PUnit tensorUnitSystem.carrier tensorUnitSystem.carrier where
  kraus := { operator _ := 1 }
  observe := fun _ => PUnit.unit
noncomputable def tensorPower (I : FiniteInstrument κ Ω H K) : (n : Nat) →
    FiniteInstrument (tensorPowerHistory κ n) (tensorPowerHistory Ω n)
      (tensorPowerCarrier H n) (tensorPowerCarrier K n)
  | 0 => tensorUnitInstrument
  | n + 1 => I.tensor (tensorPower I n)
end TensorPower
end FiniteInstrument
end
end Semantics
end QEC



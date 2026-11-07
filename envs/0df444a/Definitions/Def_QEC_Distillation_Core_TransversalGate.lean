-- Prove2me | Definitions.Def_QEC_Distillation_Core_TransversalGate
-- name    : QEC_Distillation_Core_TransversalGate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:12:33.061999+00:00
-- url     : https://prove2.me/theorems/c5f2c802-8e36-420e-87eb-38340355cf3d
-- title:
--   Transversal Gate
-- statement:
--   Definitions and structural lemmas for Transversal Gate, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/TransversalGate.lean

import Definitions.Def_QEC_Semantics_Core_Definitions
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
universe u
namespace QEC
namespace Semantics
namespace UnitaryTransport
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
def identity (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] : UnitaryTransport H H where
  toLinearEquiv := LinearEquiv.refl Complex H
  map_inner := by
    intro x y
    rfl
@[simp]
theorem identity_apply (x : H) : identity H x = x :=
  rfl
def trans (U : UnitaryTransport H K) (V : UnitaryTransport K L) :
    UnitaryTransport H L where
  toLinearEquiv := U.toLinearEquiv.trans V.toLinearEquiv
  map_inner := by
    intro x y
    exact (V.map_inner (U x) (U y)).trans (U.map_inner x y)
@[simp]
theorem trans_apply (U : UnitaryTransport H K) (V : UnitaryTransport K L) (x : H) :
    U.trans V x = V (U x) :=
  rfl
end UnitaryTransport
end Semantics
namespace Distillation
open Semantics
variable {Logical Physical Site : Type u}
variable [NormedAddCommGroup Logical] [InnerProductSpace Complex Logical]
variable [FiniteQuantumSystem Logical]
variable [NormedAddCommGroup Physical] [InnerProductSpace Complex Physical]
variable [FiniteQuantumSystem Physical]
structure EncodedCode (Logical Physical : Type u)
    [NormedAddCommGroup Logical] [InnerProductSpace Complex Logical]
    [FiniteQuantumSystem Logical]
    [NormedAddCommGroup Physical] [InnerProductSpace Complex Physical]
    [FiniteQuantumSystem Physical] where
  code : QuantumCode Physical
  encoding : Logical ≃ₗᵢ[Complex] code.carrier
namespace EncodedCode
def encode (E : EncodedCode Logical Physical) (psi : Logical) : Physical :=
  E.encoding psi
@[simp]
theorem encode_mem (E : EncodedCode Logical Physical) (psi : Logical) :
    E.encode psi ∈ E.code.carrier :=
  (E.encoding psi).property
def ImplementsLogicalGate (E : EncodedCode Logical Physical)
    (physical : UnitaryTransport Physical Physical)
    (logical : UnitaryTransport Logical Logical) : Prop :=
  ∀ psi : Logical, physical (E.encode psi) = E.encode (logical psi)
namespace ImplementsLogicalGate
theorem identity (E : EncodedCode Logical Physical) :
    E.ImplementsLogicalGate (UnitaryTransport.identity Physical)
      (UnitaryTransport.identity Logical) := by
  intro psi
  rfl
theorem trans (E : EncodedCode Logical Physical)
    {physical₁ physical₂ : UnitaryTransport Physical Physical}
    {logical₁ logical₂ : UnitaryTransport Logical Logical}
    (h₁ : E.ImplementsLogicalGate physical₁ logical₁)
    (h₂ : E.ImplementsLogicalGate physical₂ logical₂) :
    E.ImplementsLogicalGate (physical₁.trans physical₂) (logical₁.trans logical₂) := by
  intro psi
  simp only [UnitaryTransport.trans_apply]
  rw [h₁ psi, h₂ (logical₁ psi)]
end ImplementsLogicalGate
end EncodedCode
namespace UnitaryTransport
def composeList : List (UnitaryTransport Physical Physical) →
    UnitaryTransport Physical Physical
  | [] => Semantics.UnitaryTransport.identity Physical
  | gate :: gates => gate.trans (composeList gates)
def composeFamily {n : Nat} (gates : Fin n → UnitaryTransport Physical Physical) :
    UnitaryTransport Physical Physical :=
  composeList (List.ofFn gates)
end UnitaryTransport
structure FinitePhysicalGateModel (Site Physical : Type u)
    [Fintype Site] [DecidableEq Site]
    [NormedAddCommGroup Physical] [InnerProductSpace Complex Physical]
    [FiniteQuantumSystem Physical] where
  LocalGate : Finset Site → Type u
  realize : {support : Finset Site} → LocalGate support →
    UnitaryTransport Physical Physical
structure LocalGateFactor [Fintype Site] [DecidableEq Site]
    (model : FinitePhysicalGateModel Site Physical) where
  support : Finset Site
  gate : model.LocalGate support
namespace LocalGateFactor
def realized [Fintype Site] [DecidableEq Site]
    {model : FinitePhysicalGateModel Site Physical}
    (factor : LocalGateFactor model) : UnitaryTransport Physical Physical :=
  model.realize factor.gate
end LocalGateFactor
structure PhysicalGateFactorization [Fintype Site] [DecidableEq Site]
    (model : FinitePhysicalGateModel Site Physical)
    (physical : UnitaryTransport Physical Physical) where
  factorCount : Nat
  support : Fin factorCount → Finset Site
  factor : (j : Fin factorCount) → model.LocalGate (support j)
  pairwise_disjoint : ∀ ⦃i j : Fin factorCount⦄, i ≠ j →
    Disjoint (support i) (support j)
  realizes :
    UnitaryTransport.composeFamily (fun j => model.realize (factor j)) = physical
structure FiniteBlockDecomposition (Site : Type u) [Fintype Site] [DecidableEq Site] where
  blockCount : Nat
  sites : Fin blockCount → Finset Site
  pairwise_disjoint : ∀ ⦃i j : Fin blockCount⦄, i ≠ j → Disjoint (sites i) (sites j)
  covers : Finset.univ.biUnion sites = Finset.univ
structure SitewiseTransversalityData [Fintype Site] [DecidableEq Site]
    (model : FinitePhysicalGateModel Site Physical)
    (physical : UnitaryTransport Physical Physical)
    extends PhysicalGateFactorization model physical where
  support_card_le_one : ∀ j, (toPhysicalGateFactorization.support j).card ≤ 1
structure BlockTransversalityData [Fintype Site] [DecidableEq Site]
    (model : FinitePhysicalGateModel Site Physical)
    (physical : UnitaryTransport Physical Physical)
    (blocks : FiniteBlockDecomposition Site)
    extends PhysicalGateFactorization model physical where
  support_within_block : ∀ j, ∃ b,
    toPhysicalGateFactorization.support j ⊆ blocks.sites b
structure SubsetTransversalityData [Fintype Site] [DecidableEq Site]
    (model : FinitePhysicalGateModel Site Physical)
    (physical : UnitaryTransport Physical Physical)
    (permittedSupports : Finset (Finset Site))
    extends PhysicalGateFactorization model physical where
  support_permitted : ∀ j,
    toPhysicalGateFactorization.support j ∈ permittedSupports
structure SitewiseTransversalLogicalGate [Fintype Site] [DecidableEq Site]
    (E : EncodedCode Logical Physical)
    (logical : UnitaryTransport Logical Logical)
    (model : FinitePhysicalGateModel Site Physical) where
  physicalGate : UnitaryTransport Physical Physical
  implements : E.ImplementsLogicalGate physicalGate logical
  transversality : SitewiseTransversalityData model physicalGate
structure BlockTransversalLogicalGate [Fintype Site] [DecidableEq Site]
    (E : EncodedCode Logical Physical)
    (logical : UnitaryTransport Logical Logical)
    (model : FinitePhysicalGateModel Site Physical)
    (blocks : FiniteBlockDecomposition Site) where
  physicalGate : UnitaryTransport Physical Physical
  implements : E.ImplementsLogicalGate physicalGate logical
  transversality : BlockTransversalityData model physicalGate blocks
structure SubsetTransversalLogicalGate [Fintype Site] [DecidableEq Site]
    (E : EncodedCode Logical Physical)
    (logical : UnitaryTransport Logical Logical)
    (model : FinitePhysicalGateModel Site Physical)
    (permittedSupports : Finset (Finset Site)) where
  physicalGate : UnitaryTransport Physical Physical
  implements : E.ImplementsLogicalGate physicalGate logical
  transversality : SubsetTransversalityData model physicalGate permittedSupports
end Distillation
end QEC



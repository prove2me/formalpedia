-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Sequential_DependentComposition
-- name    : QEC_Semantics_Instruments_Sequential_DependentComposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:39:46.657985+00:00
-- url     : https://prove2.me/theorems/cba2be86-b8bb-48a7-ab05-0a93b5268aa1
-- title:
--   Dependent Composition
-- statement:
--   Definitions and structural lemmas for Dependent Composition, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/DependentComposition.lean

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
set_option autoImplicit false
universe u v w x y
namespace QEC
namespace Semantics
open scoped BigOperators ComplexOrder
noncomputable section
namespace FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {κ₂ : Ω → Type x} [∀ outcome, Fintype (κ₂ outcome)]
variable {Ξ : Ω → Type y} [∀ outcome, Fintype (Ξ outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
noncomputable def bindDependent (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) (Ξ outcome) K L) :
    FiniteInstrument (Sigma fun firstIndex : κ => κ₂ (I.observe firstIndex)) (Sigma Ξ) H L where
  kraus :=
    { operator index :=
      ((J (I.observe index.1)).kraus.operator index.2).comp
        (I.kraus.operator index.1) }
  observe := fun index =>
    ⟨I.observe index.1, (J (I.observe index.1)).observe index.2⟩
end FiniteInstrument
end
end Semantics
end QEC



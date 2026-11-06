-- Prove2me | Definitions.Def_QEC_Coding_CSS_Subsystem
-- name    : QEC_Coding_CSS_Subsystem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:58:50.897303+00:00
-- url     : https://prove2.me/theorems/afcaa29c-953a-4b4f-bde2-16cbe30aa248
-- title:
--   Subsystem
-- statement:
--   Definitions and structural lemmas for Subsystem, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Subsystem.lean

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
set_option autoImplicit false
namespace QEC.Coding
universe u v
structure SubsystemCSSData
    (i0 i1 i2 : Type u) (LogicalZ LogicalX : Type v)
    [Fintype i0] [Fintype i1] [Fintype i2]
    [AddCommGroup LogicalZ] [Module (ZMod 2) LogicalZ]
    [AddCommGroup LogicalX] [Module (ZMod 2) LogicalX]
    [Module.Finite (ZMod 2) LogicalZ] [Module.Finite (ZMod 2) LogicalX] where
  /-- The actual stabilizer chain complex. -/
  complex : ChainComplexData (ZMod 2)
    (Word (ZMod 2) i0) (Word (ZMod 2) i1) (Word (ZMod 2) i2)
  /-- Projection from ordinary `Z` homology to the selected logical sector. -/
  homologyProjection : complex.middleHomology →ₗ[ZMod 2] LogicalZ
  /-- Projection from ordinary `X` cohomology to the selected logical sector. -/
  cohomologyProjection : complex.middleCohomology →ₗ[ZMod 2] LogicalX
  homologyProjection_surjective : Function.Surjective homologyProjection
  cohomologyProjection_surjective : Function.Surjective cohomologyProjection
  /-- The selected `Z` and `X` sectors encode the same number of qubits. -/
  logical_finrank_eq :
    Module.finrank (ZMod 2) LogicalZ = Module.finrank (ZMod 2) LogicalX
namespace SubsystemCSSData
variable {i0 i1 i2 : Type u} {LogicalZ LogicalX : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]
variable [AddCommGroup LogicalZ] [Module (ZMod 2) LogicalZ]
variable [AddCommGroup LogicalX] [Module (ZMod 2) LogicalX]
variable [Module.Finite (ZMod 2) LogicalZ] [Module.Finite (ZMod 2) LogicalX]
noncomputable def homologyGaugeSector
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) :
    Submodule (ZMod 2) D.complex.middleHomology :=
  LinearMap.ker D.homologyProjection
noncomputable def cohomologyGaugeSector
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) :
    Submodule (ZMod 2) D.complex.middleCohomology :=
  LinearMap.ker D.cohomologyProjection
noncomputable def logicalQubits
    (_D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) : Nat :=
  Module.finrank (ZMod 2) LogicalZ
def DressedZDistanceAtLeast
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat) : Prop :=
  ∀ (z : Word (ZMod 2) i1)
      (hz : z ∈ D.complex.middleCycleCode.carrier),
    D.homologyProjection
        (D.complex.middleBoundaryInCycles.mkQ ⟨z, hz⟩) ≠ 0 →
      d ≤ HammingWeight z
def DressedXDistanceAtLeast
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat) : Prop :=
  ∀ (x : Word (ZMod 2) i1)
      (hx : x ∈ D.complex.middleCocycleCode.carrier),
    D.cohomologyProjection
        (D.complex.middleCoboundaryInCocycles.mkQ ⟨x, hx⟩) ≠ 0 →
      d ≤ HammingWeight x
end SubsystemCSSData
end QEC.Coding



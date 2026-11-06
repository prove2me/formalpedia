-- Prove2me | Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
-- name    : QEC_Coding_ChainComplex_HomotopyDistance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:57:25.130802+00:00
-- url     : https://prove2.me/theorems/6e076bd7-fabe-4aed-8757-8ef29a87b0e2
-- title:
--   Homotopy Distance
-- statement:
--   Definitions and structural lemmas for Homotopy Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/HomotopyDistance.lean

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
set_option autoImplicit false
namespace QEC.Coding
universe u v w
def MiddleHomologyDistanceAtLeast
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    {ι0 ι1 ι2 : Type v} [Fintype ι0] [Fintype ι1] [Fintype ι2]
    (K : ChainComplexData F (Word F ι0) (Word F ι1) (Word F ι2))
    (d : Nat) : Prop :=
  ∀ z : Word F ι1,
    z ∈ K.middleCycleCode.carrier →
    z ∉ K.middleBoundaryCode.carrier →
    d ≤ HammingWeight z
def MiddleCohomologyDistanceAtLeast
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    {ι0 ι1 ι2 : Type v} [Fintype ι0] [Fintype ι1] [Fintype ι2]
    (K : ChainComplexData F (Word F ι0) (Word F ι1) (Word F ι2))
    (d : Nat) : Prop :=
  ∀ x : Word F ι1,
    x ∈ K.middleCocycleCode.carrier →
    x ∉ K.firstCoboundaryCheckCode.carrier →
    d ≤ HammingWeight x
namespace ThreeTermChainHomotopyEquiv
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {ι0 ι1 ι2 : Type v} [Fintype ι0] [Fintype ι1] [Fintype ι2]
variable {κ0 κ1 κ2 : Type w} [Fintype κ0] [Fintype κ1] [Fintype κ2]
variable {A : ChainComplexData F (Word F ι0) (Word F ι1) (Word F ι2)}
variable {B : ChainComplexData F (Word F κ0) (Word F κ1) (Word F κ2)}
end ThreeTermChainHomotopyEquiv
end QEC.Coding



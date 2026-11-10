-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T11:30:46.411189+00:00
-- url     : https://prove2.me/theorems/60ccdf57-f654-4340-8c00-2c209c22f56c
-- title:
--   Cubic Phase
-- statement:
--   Definitions and structural lemmas for Cubic Phase, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CubicPhase.lean

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CCZIntertwining
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Distillation_coordinateSupport_disjoint

set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Ngu24MultiplicativeCCZ
open Coding Semantics Ngu24MultiplicativeCSS
open scoped BigOperators
universe u
variable {F J I Logical : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  [Fintype J] [DecidableEq J]
def taggedCubicPhaseExponent (sites : Finset J)
    (label : TaggedThreeCopyRegisterLabel F J) : F :=
  ∑ j ∈ sites, label (.first, j) * label (.second, j) * label (.third, j)
def taggedCubicPhaseAmplitude (f : F →ₗ[ZMod 2] ZMod 2) (sites : Finset J)
    (label : TaggedThreeCopyRegisterLabel F J) : Complex :=
  PauliSymplectic.binaryPhaseScalar (f (taggedCubicPhaseExponent sites label))
theorem binaryPhaseScalar_mul_self (p : ZMod 2) :
    PauliSymplectic.binaryPhaseScalar p * PauliSymplectic.binaryPhaseScalar p = 1 := by
  rw [← PauliSymplectic.binaryPhaseScalar_add]
  have hp : p + p = 0 := by fin_cases p <;> decide
  rw [hp, PauliSymplectic.binaryPhaseScalar_zero]
def taggedCubicPhaseTransport (f : F →ₗ[ZMod 2] ZMod 2) (sites : Finset J) :
    UnitaryTransport (TaggedThreeCopyRegister F J) (TaggedThreeCopyRegister F J) where
  toLinearEquiv := KT19PrimeQuditCSS.diagonalLinearEquiv
    (taggedCubicPhaseAmplitude f sites) (taggedCubicPhaseAmplitude f sites)
    (fun _ => binaryPhaseScalar_mul_self _) (fun _ => binaryPhaseScalar_mul_self _)
  map_inner := KT19PrimeQuditCSS.diagonalOperator_map_inner _ (fun label => by
    change PauliSymplectic.binaryPhaseScalar _ *
      star (PauliSymplectic.binaryPhaseScalar _) = 1
    rw [PauliSymplectic.binaryPhaseScalar_star]
    exact binaryPhaseScalar_mul_self _)
def taggedCubicPhysicalTransport (f : F →ₗ[ZMod 2] ZMod 2) :
    UnitaryTransport (TaggedThreeCopyRegister F J) (TaggedThreeCopyRegister F J) :=
  UnitaryTransport.composeFamily fun j : Fin (Fintype.card J) =>
    taggedCubicPhaseTransport f {taggedCczSiteEquivFin J j}
inductive TaggedCubicLocalGate : Finset (TaggedThreeCopyCoordinate J) → Type u
  | at (site : J) : TaggedCubicLocalGate (coordinateSupport site)
def taggedCubicPhysicalGateModel (f : F →ₗ[ZMod 2] ZMod 2) :
    FinitePhysicalGateModel (TaggedThreeCopyCoordinate J) (TaggedThreeCopyRegister F J) where
  LocalGate := TaggedCubicLocalGate
  realize gate := match gate with
    | .at site => taggedCubicPhaseTransport f {site}
def taggedCubicPhysicalFactorization (f : F →ₗ[ZMod 2] ZMod 2) :
    PhysicalGateFactorization (taggedCubicPhysicalGateModel (J := J) f)
      (taggedCubicPhysicalTransport f) where
  factorCount := Fintype.card J
  support j := coordinateSupport (taggedCczSiteEquivFin J j)
  factor j := .at (taggedCczSiteEquivFin J j)
  pairwise_disjoint := by
    intro i j hij
    exact coordinateSupport_disjoint ((taggedCczSiteEquivFin J).injective.ne hij)
  realizes := rfl
section Encoding
variable [Fintype I] [Fintype Logical] [CharP F 2]
local instance _p2m_local_instance_bfada1b37a_179 : DecidableEq Logical := Classical.decEq _
end Encoding
end QEC.Distillation.Ngu24MultiplicativeCCZ



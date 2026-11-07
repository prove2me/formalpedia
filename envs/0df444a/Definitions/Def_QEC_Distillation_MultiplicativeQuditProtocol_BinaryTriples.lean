-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:46:28.92467+00:00
-- url     : https://prove2.me/theorems/34110cb9-4518-4f2c-989a-ef2b3ab41e53
-- title:
--   Binary Triples
-- statement:
--   Definitions and structural lemmas for Binary Triples, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTriples.lean

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Ngu24Binary
open Coding
open scoped BigOperators
universe u
variable (J : Type u)
def binaryPi2 : Equiv.Perm (J × Fin 512) :=
  (Equiv.refl J).prodCongr f256MFEpi2.symm
def binaryPi3 : Equiv.Perm (J × Fin 512) :=
  (Equiv.refl J).prodCongr f256MFEpi3.symm
def binaryTripleVertex (x : J × Fin 512) (tag : ThreeCopyTag) :
    TaggedThreeCopyCoordinate (J × Fin 512) :=
  (tag, match tag with
    | .first => x
    | .second => (binaryPi2 J).symm x
    | .third => (binaryPi3 J).symm x)
theorem binaryTripleVertex_injective (x : J × Fin 512) :
    Function.Injective (binaryTripleVertex J x) := by
  intro a b h
  exact congrArg Prod.fst h
variable [Fintype J]
def binaryTripleSupport (x : J × Fin 512) : Finset (TaggedThreeCopyCoordinate (J × Fin 512)) :=
  Finset.univ.map ⟨binaryTripleVertex J x, binaryTripleVertex_injective J x⟩
def binarySelectedSites : Finset (J × Fin 512) :=
  Finset.univ.product f256SelectedCoordinates
end QEC.Distillation.Ngu24Binary



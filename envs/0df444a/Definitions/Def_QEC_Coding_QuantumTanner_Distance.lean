-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_Distance
-- name    : QEC_Coding_QuantumTanner_Distance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:14:00.283632+00:00
-- url     : https://prove2.me/theorems/6184d086-2514-4a86-a90e-61a3276548be
-- title:
--   Distance
-- statement:
--   Definitions and structural lemmas for Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner
open Classical
universe v
namespace LeftRightCayleySquareComplex
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
def localRestriction (X : LeftRightCayleySquareComplex G A B Square)
    (vertex : G × Bool) : Word (ZMod 2) Square →ₗ[ZMod 2] Word (ZMod 2) (A × B) where
  toFun x ab := x (X.link vertex ab)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def activeVerticesOnSide (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) : Finset G :=
  Finset.univ.filter fun g => X.localRestriction (g, side) x ≠ 0
end LeftRightCayleySquareComplex
namespace RawData
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]
end RawData
namespace Data
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]
end Data
end QEC.Coding.QuantumTanner



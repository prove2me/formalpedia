-- Prove2me | Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
-- name    : QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:33:51.013567+00:00
-- url     : https://prove2.me/theorems/a64282e9-85d7-4f82-98b9-78a180acccdf
-- title:
--   Boundary Maps
-- statement:
--   Definitions and structural lemmas for Boundary Maps, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/BoundaryMaps.lean

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Realization
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HypergraphProduct
universe u v
open TensorProduct
def jointTensorWordMap
    {F : Type v} {A A' B B' : Type u}
    [Field F] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    (f : Word F A →ₗ[F] Word F A') (g : Word F B →ₗ[F] Word F B') :
    (Word F A ⊗[F] Word F B) →ₗ[F]
      Word F (A' × B) × Word F (A × B') :=
  ((wordTensorEquiv F A' B).prodCongr
      (wordTensorEquiv F A B')).toLinearMap.comp
    (jointTensorMap f g)
def boundary1TransposeTensorMap
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    (Word (ZMod 2) rowOne ⊗[ZMod 2] Word (ZMod 2) colTwo) →ₗ[ZMod 2]
      Word (ZMod 2) (colOne × colTwo) ×
        Word (ZMod 2) (rowOne × rowTwo) :=
  (wordSumEquiv (ZMod 2) (colOne × colTwo) (rowOne × rowTwo)).toLinearMap.comp
    ((wordLinearMapTranspose (boundary1 D)).comp
      (wordTensorEquiv (ZMod 2) rowOne colTwo).toLinearMap)
def boundary2TensorMap
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    (Word (ZMod 2) colOne ⊗[ZMod 2] Word (ZMod 2) rowTwo) →ₗ[ZMod 2]
      Word (ZMod 2) (rowOne × rowTwo) ×
        Word (ZMod 2) (colOne × colTwo) :=
  (wordSumEquivSwap (ZMod 2) (colOne × colTwo)
      (rowOne × rowTwo)).toLinearMap.comp
    ((boundary2 D).comp
      (wordTensorEquiv (ZMod 2) colOne rowTwo).toLinearMap)
end QEC.Coding.HypergraphProduct



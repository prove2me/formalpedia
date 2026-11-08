-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
-- name    : QEC_Coding_ExpanderCodes_LocalParameterSelection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:13:41.338973+00:00
-- url     : https://prove2.me/theorems/9c1bd4f2-0fb9-4566-a6cb-57c1785305bb
-- title:
--   Local Parameter Selection
-- statement:
--   Definitions and structural lemmas for Local Parameter Selection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
def pk22ParameterBase (q t : Nat) : Nat := 2 * q ^ t + 1
def pk22LocalWidth (q t : Nat) : Nat := (pk22ParameterBase q t) ^ 4
def pk22SpectralCoefficient (q t : Nat) : Nat :=
  16 * (pk22ParameterBase q t) ^ 2
def pk22FaceCoefficient (q t : Nat) : Nat :=
  112 * (pk22SpectralCoefficient q t) ^ 2
def pk22DistanceCoefficient (q t : Nat) : Nat :=
  32 * pk22SpectralCoefficient q t
def pk22RowCoefficient (q t : Nat) : Nat :=
  logarithmicLocalRows q (pk22LocalWidth q t) (pk22DistanceCoefficient q t)
def pk22RectangleConstant (q t : Nat) : Nat :=
  let A := pk22LocalWidth q t
  let S := pk22FaceCoefficient q t
  2 * (64 * A) + 2 * (64 * A) * S + 4 * 1 * (64 * A) +
    16 * S + 11
def pk22ScaleThreshold (q t : Nat) : Nat :=
  let A := pk22LocalWidth q t
  let C := pk22SpectralCoefficient q t
  let S := pk22FaceCoefficient q t
  18 + 4 * S + (C + 2) + 4 * C + (128 * A + 1) +
    (pk22RectangleConstant q t + 1)
end QEC.Coding.TannerLiftedProduct



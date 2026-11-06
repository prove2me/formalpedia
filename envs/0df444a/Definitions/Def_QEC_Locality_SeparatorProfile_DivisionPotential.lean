-- Prove2me | Definitions.Def_QEC_Locality_SeparatorProfile_DivisionPotential
-- name    : QEC_Locality_SeparatorProfile_DivisionPotential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:10:29.918242+00:00
-- url     : https://prove2.me/theorems/b295153a-f5f6-4838-810e-e575cface262
-- title:
--   Division Potential
-- statement:
--   Definitions and structural lemmas for Division Potential, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/DivisionPotential.lean

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
set_option autoImplicit false
noncomputable section
namespace QEC.Locality
def profileDivisionRpowGap (exponent : ℝ) : ℝ :=
  (3 / 4 : ℝ) ^ exponent + (1 / 4 : ℝ) ^ exponent - 1
def profileDivisionPotentialCoefficient (beta exponent : ℝ) : ℝ :=
  4 * beta / profileDivisionRpowGap exponent
def profileDivisionPotential
    (beta exponent : ℝ) (r parent : Nat) : ℝ :=
  profileDivisionPotentialCoefficient beta exponent * (r : ℝ) ^ exponent *
    (((parent : ℝ) / r) / (1 / 4 : ℝ) ^ (1 - exponent) -
      ((parent : ℝ) / r) ^ exponent)
noncomputable def profileDivisionThreshold (beta exponent : ℝ) : Nat :=
  max (profileSeparatorThreshold beta exponent)
    (Nat.ceil
      ((profileDivisionPotentialCoefficient beta exponent /
          (1 / 4 : ℝ) ^ (1 - exponent)) ^ ((1 - exponent)⁻¹)))
end QEC.Locality



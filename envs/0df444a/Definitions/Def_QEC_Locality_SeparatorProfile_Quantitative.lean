-- Prove2me | Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
-- name    : QEC_Locality_SeparatorProfile_Quantitative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:09:17.614204+00:00
-- url     : https://prove2.me/theorems/940081da-e0ad-4e78-b2a4-db181d90daba
-- title:
--   Quantitative
-- statement:
--   Definitions and structural lemmas for Quantitative, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Quantitative.lean

import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
set_option autoImplicit false
namespace QEC.Locality
universe u
noncomputable def separatorLeftEdges {ι : Type u} [DecidableEq ι]
    (edges : Finset (ι × ι)) (left : Finset ι) : Finset (ι × ι) :=
  edges.filter fun edge => edge.1 ∈ left ∨ edge.2 ∈ left
noncomputable def separatorRightEdges {ι : Type u} [DecidableEq ι]
    (edges : Finset (ι × ι)) (left : Finset ι) : Finset (ι × ι) :=
  edges.filter fun edge => ¬ (edge.1 ∈ left ∨ edge.2 ∈ left)
noncomputable def profileSeparatorThreshold (beta exponent : ℝ) : Nat :=
  Nat.ceil ((12 * beta) ^ ((1 - exponent)⁻¹))
end QEC.Locality



-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewResidueCoordinates
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewResidueCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T14:16:28.145946+00:00
-- url     : https://prove2.me/theorems/9fb9a9fb-4373-4093-9a6e-2ec5f931baae
-- title:
--   Skew Residue Coordinates
-- statement:
--   Definitions and structural lemmas for Skew Residue Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewResidueCoordinates.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank

set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
noncomputable def skewExponentResidue
    (r : Rank) (n : ℤ) : Fin r.matrixRank := by
  have hdNat : 0 < r.matrixRank :=
    lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)
  have hd : (0 : ℤ) < (r.matrixRank : ℤ) := by exact_mod_cast hdNat
  exact ⟨(n % (r.matrixRank : ℤ)).toNat,
    (Int.toNat_lt_of_ne_zero (ne_of_gt hdNat)).2
      (Int.emod_lt_of_pos n hd)⟩
noncomputable def skewExponentQuotient
    (r : Rank) (n : ℤ) : ℤ := n / (r.matrixRank : ℤ)
noncomputable def skewLaurentCyclicLaurentCoordinate
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    LaurentPolynomial (BaseField P) :=
  f.sum fun n c =>
    if skewExponentResidue r n.toAdd = p.2 then
      LaurentPolynomial.C ((constantBasis P r).repr c p.1) *
      LaurentPolynomial.T (skewExponentQuotient r n.toAdd)
    else 0
end QEC.Coding.HighDimensionalExpander.CartwrightSteger



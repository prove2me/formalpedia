-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:51:02.116997+00:00
-- url     : https://prove2.me/theorems/8e947df7-4d9b-45af-8b9a-14c3e797aa15
-- title:
--   Skew Units
-- statement:
--   Definitions and structural lemmas for Skew Units, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewUnits.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Multiplicative SkewMonoidAlgebra
noncomputable def skewLaurentIntSupport
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r) : Finset ℤ :=
  f.support.map ⟨Multiplicative.toAdd, Multiplicative.toAdd.injective⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger



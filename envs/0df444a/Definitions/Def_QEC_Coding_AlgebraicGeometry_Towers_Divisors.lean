-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Divisors
-- name    : QEC_Coding_AlgebraicGeometry_Towers_Divisors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:14:17.547266+00:00
-- url     : https://prove2.me/theorems/36d67918-38a2-4b82-b1e5-ce11cd3c1c2b
-- title:
--   Divisors
-- statement:
--   Definitions and structural lemmas for Divisors, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Divisors.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Enumeration
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
noncomputable section
noncomputable def selectedDivisor (i : ℕ) :
    Divisor (GlobalPlace F256 (Field (i + 2))) := by
  classical
  exact ∑ j : Fin (selectedLength i),
    Finsupp.single (selectedPlace i j) (1 : ℤ)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth



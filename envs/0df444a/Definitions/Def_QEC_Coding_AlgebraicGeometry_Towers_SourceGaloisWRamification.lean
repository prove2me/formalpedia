-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:09:22.306214+00:00
-- url     : https://prove2.me/theorems/d65a71d3-d529-423f-9483-702775107131
-- title:
--   Source Galois WRamification
-- statement:
--   Definitions and structural lemmas for Source Galois WRamification, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWRamification.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWGlobalPlaces
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
abbrev sourceGaloisWRamification_E (m : ℕ) := SourceGaloisClosureField m
noncomputable def sourceGaloisSeedCoordinate (m : ℕ) : sourceGaloisWRamification_E m :=
  sourceGaloisSeedRatFuncToClosure m RatFunc.X
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth



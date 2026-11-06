-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureFiniteCompositum
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureFiniteCompositum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:23:20.09021+00:00
-- url     : https://prove2.me/theorems/b80247cb-0c57-472f-84cb-49a08684c0aa
-- title:
--   Source Normal Closure Finite Compositum
-- statement:
--   Definitions and structural lemmas for Source Normal Closure Finite Compositum, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceNormalClosureFiniteCompositum.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Mathlib.Order.CompactlyGenerated.Basic
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
noncomputable def sourceGaloisConjugateCompositum (m : ℕ)
    (s : Finset (SourceField m →ₐ[GaloisBaseField]
      SourceGaloisClosureAmbient)) :
    IntermediateField GaloisBaseField SourceGaloisClosureAmbient :=
  ⨆ f ∈ s, f.fieldRange
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth



-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:38.364594+00:00
-- url     : https://prove2.me/theorems/36f10e54-fddc-4aa8-a091-61196fb2e2f3
-- title:
--   Int Unit Of Mul Lat
-- statement:
--   Definitions and structural lemmas for Int Unit Of Mul Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntUnitOfMulLat.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
namespace GlobalTheory.HullClasses
variable {K : UQ} (B : InvAlg K)
abbrev abelian₂ : Submodule K.O B.A := Subalgebra.toSubmodule (integralClosure K.O B.A)
end GlobalTheory.HullClasses
noncomputable section
namespace GlobalTheory.HullClasses
end GlobalTheory.HullClasses



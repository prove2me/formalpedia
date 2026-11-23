-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_Hilbert90SUnitsQuadraticExtension
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_Hilbert90SUnitsQuadraticExtension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:19:28.873883+00:00
-- url     : https://prove2.me/theorems/3dc7f2fb-f063-483e-8b5c-41ec25ea2d4a
-- title:
--   Hilbert90 SUnits Quadratic Extension
-- statement:
--   Definitions and structural lemmas for Hilbert90 SUnits Quadratic Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/Hilbert90SUnitsQuadraticExtension.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationUnramifiedOfUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuationEqOfAdm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
namespace GlobalTheory.QNorm
end GlobalTheory.QNorm



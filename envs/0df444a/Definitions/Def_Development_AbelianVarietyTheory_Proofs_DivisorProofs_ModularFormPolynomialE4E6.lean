-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModularFormPolynomialE4E6
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModularFormPolynomialE4E6
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:12.880859+00:00
-- url     : https://prove2.me/theorems/2e32af2b-86f8-4695-9a4d-76ffc21728fa
-- title:
--   Modular Form Polynomial E4 E6
-- statement:
--   Definitions and structural lemmas for Modular Form Polynomial E4 E6, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModularFormPolynomialE4E6.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_ReciprocityTheory_DualLattices_QExpansionMonoWCoeffZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (IsMF)
open ModularForm (E₄ E₆)
namespace GlobalTheory.QFam
end GlobalTheory.QFam



-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionNormalizedWeierstrassPTorsion
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionNormalizedWeierstrassPTorsion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:38.17125+00:00
-- url     : https://prove2.me/theorems/d9895bf4-0c86-4f78-98e4-a04437c7bbce
-- title:
--   Has QExpansion Normalized Weierstrass PTorsion
-- statement:
--   Definitions and structural lemmas for Has QExpansion Normalized Weierstrass PTorsion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionNormalizedWeierstrassPTorsion.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassDivisionValueQExpansionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassConstantQExpansionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
namespace GlobalTheory.WpFam.ExpP
end GlobalTheory.WpFam.ExpP



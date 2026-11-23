-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_SgAlgebraMap
-- name    : ReciprocityTheory_DualLattices_SgAlgebraMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:04.438484+00:00
-- url     : https://prove2.me/theorems/ca687028-613b-44d6-8666-ff7b5536e414
-- title:
--   Sg Algebra Map
-- statement:
--   Definitions and structural lemmas for Sg Algebra Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SgAlgebraMap.lean

import Definitions.Def_ReciprocityTheory_DualLattices_EigPowEqOne
import Definitions.Def_ReciprocityTheory_DualLattices_IsAdicCompleteOfBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix Polynomial
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField



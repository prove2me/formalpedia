-- Prove2me | Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyMax
-- name    : ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyMax
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:57.077928+00:00
-- url     : https://prove2.me/theorems/b040f920-ee3d-49b0-8562-e643e8a5fc5f
-- title:
--   Poly Max
-- statement:
--   Definitions and structural lemmas for Poly Max, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/PolyMax.lean

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.CA
open Polynomial IsLocalRing
variable {P : Type*} [CommRing P] [IsLocalRing P]
end ReciprocityTheory.CA



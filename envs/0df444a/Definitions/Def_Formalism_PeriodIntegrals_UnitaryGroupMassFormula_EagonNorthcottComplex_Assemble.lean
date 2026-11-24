-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_Assemble
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_Assemble
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:46.507795+00:00
-- url     : https://prove2.me/theorems/d3a68601-0b64-40fb-87a5-9a6e526bc015
-- title:
--   Assemble
-- statement:
--   Definitions and structural lemmas for Assemble, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/Assemble.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace PIW.ENSpec
open PI.EagonNorthcott MvPolynomial RingTheory.Sequence
section Nat
variable {R : Type u} [CommRing R] {D : ℕ} (x : Fin D → R)
end Nat
end PIW.ENSpec



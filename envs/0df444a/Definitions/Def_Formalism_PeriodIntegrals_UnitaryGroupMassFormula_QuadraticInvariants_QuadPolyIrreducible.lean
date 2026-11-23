-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticInvariants_QuadPolyIrreducible
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticInvariants_QuadPolyIrreducible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:17.398424+00:00
-- url     : https://prove2.me/theorems/f1ec2453-9a85-4542-9b20-c297d73a9190
-- title:
--   Quad Poly Irreducible
-- statement:
--   Definitions and structural lemmas for Quad Poly Irreducible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticInvariants/QuadPolyIrreducible.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
namespace PI.UnitaryGroupMassFormula.ClassNumImQInv
open PI.ClassNumImQ
variable {d : ℕ} {K : Type} [Field K] [NumberField K] {b : K}
noncomputable def quadPoly (d : ℕ) : ℚ[X] := X ^ 2 + C (d : ℚ)
end PI.UnitaryGroupMassFormula.ClassNumImQInv



-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExponentInequalityNondegenerateMid
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExponentInequalityNondegenerateMid
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:22:43.484276+00:00
-- url     : https://prove2.me/theorems/5758908f-c8a9-4746-8bf5-a5b3f09a537f
-- title:
--   Exponent Inequality Nondegenerate Mid
-- statement:
--   Definitions and structural lemmas for Exponent Inequality Nondegenerate Mid, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExponentInequalityNondegenerateMid.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
noncomputable def commonLatticeBound (C : ℝ) (k m f s : ℕ) (b v Gam : ℝ) (Xi : ℕ → ℝ) : ℝ :=
  ((k : ℝ) * v) ^ (k * f) * Xi s * C ^ (k * f) *
    bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) * Gam
end Formalism.HermitianLatticeCounting.P



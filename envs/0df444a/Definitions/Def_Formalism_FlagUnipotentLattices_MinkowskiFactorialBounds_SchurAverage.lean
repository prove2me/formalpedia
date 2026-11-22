-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:25:20.984983+00:00
-- url     : https://prove2.me/theorems/62817fd0-1f3e-466f-ab5f-0b4e3b3a908b
-- title:
--   Schur Average
-- statement:
--   Definitions and structural lemmas for Schur Average, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean

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
open InnerProductSpace
section Hadamard
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
noncomputable def s5bL {r : ℕ} (a : Fin r → U) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun n i =>
    if i < n then inner ℂ (gramSchmidt ℂ a i) (a n) / ((‖gramSchmidt ℂ a i‖ : ℂ) ^ 2)
    else if i = n then 1 else 0
end Hadamard
end Formalism.HermitianLatticeCounting.P



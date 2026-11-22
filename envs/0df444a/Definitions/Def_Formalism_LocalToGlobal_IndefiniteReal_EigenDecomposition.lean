-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_EigenDecomposition
-- name    : Formalism_LocalToGlobal_IndefiniteReal_EigenDecomposition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:22.182953+00:00
-- url     : https://prove2.me/theorems/4a75b11d-761b-4f0f-a8a8-cd0bd51ee6d5
-- title:
--   Eigen Decomposition
-- statement:
--   Definitions and structural lemmas for Eigen Decomposition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/EigenDecomposition.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
namespace Formalism.IndefR.EigenDecomposition
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
noncomputable def reIm (T : H →ₗ[ℂ] H) (b : Bool) : H →ₗ[ℂ] H :=
  if b then T + LinearMap.adjoint T else Complex.I • (T - LinearMap.adjoint T)
end Formalism.IndefR.EigenDecomposition



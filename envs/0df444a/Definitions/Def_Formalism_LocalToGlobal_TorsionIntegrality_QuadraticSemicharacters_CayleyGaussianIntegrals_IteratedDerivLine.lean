-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_IteratedDerivLine
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_IteratedDerivLine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:30:31.35581+00:00
-- url     : https://prove2.me/theorems/fc9f92ad-f7be-41f2-b26c-efbce5d0f85a
-- title:
--   Iterated Deriv Line
-- statement:
--   Definitions and structural lemmas for Iterated Deriv Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/IteratedDerivLine.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
def cntVec {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ} (f : Fin k → n) : n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (Finset.univ.filter fun j => f j = i).card
end Formalism.L2.Th1.H



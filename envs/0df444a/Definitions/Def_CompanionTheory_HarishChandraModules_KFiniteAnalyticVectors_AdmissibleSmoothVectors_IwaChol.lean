-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
-- name    : CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:28.203795+00:00
-- url     : https://prove2.me/theorems/b4ecce4a-df2e-46f4-9e43-8809c2d59dfe
-- title:
--   Iwa Chol
-- statement:
--   Definitions and structural lemmas for Iwa Chol, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaChol.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace CompanionTheory.D.gk.admitted.CholeskyDecomposition
open Matrix
open scoped ComplexOrder
set_option linter.unusedSectionVars false
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]
section Existence
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]
end Existence
section Existence2
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]
end Existence2
end CompanionTheory.D.gk.admitted.CholeskyDecomposition



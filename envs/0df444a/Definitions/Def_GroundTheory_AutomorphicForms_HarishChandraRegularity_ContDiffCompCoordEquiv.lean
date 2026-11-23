-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
-- name    : GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:39.594917+00:00
-- url     : https://prove2.me/theorems/b931f997-fe21-4628-bee6-2d01d397d900
-- title:
--   Cont Diff Comp Coord Equiv
-- statement:
--   Definitions and structural lemmas for Cont Diff Comp Coord Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ContDiffCompCoordEquiv.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open scoped ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
noncomputable def coordEquiv {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    EuclideanSpace ℝ (Fin d) ≃L[ℝ] 𝔤 :=
  (EuclideanSpace.equiv (Fin d) ℝ).trans b.equivFun.symm.toContinuousLinearEquiv
namespace IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
end IsExpLieAlgebra
end GroundTheory.Automorphic



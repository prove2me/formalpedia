-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
-- name    : GroundTheory_AutomorphicForms_ReductionDirichlet
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:08:14.943498+00:00
-- url     : https://prove2.me/theorems/2bade221-9f32-537d-b522-12c59e7dcebd
-- title:
--   Reduction Dirichlet
-- statement:
--   Definitions and structural lemmas for Reduction Dirichlet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped NumberField.AdeleRing RestrictedProduct
namespace GroundTheory.Automorphic
noncomputable section
namespace Reduction
variable {K : Type*} [Field K] [NumberField K]
def posIdele (ρ : ℝ) (hρ : 0 < ρ) : IdeleGroup K :=
  ∏ w : InfinitePlace K, moduleSection w ⟨ρ ^ w.mult, pow_pos hρ _⟩
end Reduction
end
end GroundTheory.Automorphic



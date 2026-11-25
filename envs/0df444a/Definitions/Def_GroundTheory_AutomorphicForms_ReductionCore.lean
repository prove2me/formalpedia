-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_ReductionCore
-- name    : GroundTheory_AutomorphicForms_ReductionCore
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T04:32:20.90712+00:00
-- url     : https://prove2.me/theorems/f7f19954-518c-4c00-b9fe-f383d226c2e8
-- title:
--   Reduction Core
-- statement:
--   Definitions and structural lemmas for Reduction Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionBlock
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
namespace GroundTheory.Automorphic
noncomputable section
namespace Reduction
variable {K : Type*} [Field K] [NumberField K]
def adeleAbs (a : 𝔸[K]) : ℝ :=
  (∏ w : InfinitePlace K, ‖a.1 w‖ ^ w.mult) * ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖
section Two
variable {E : Type*} [NormedField E] {n : ℕ}
end Two
end Reduction
end
end GroundTheory.Automorphic



-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMinkowskiVolumeForm
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMinkowskiVolumeForm
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T02:31:11.187849+00:00
-- url     : https://prove2.me/theorems/1a6c76f6-9eb4-56a3-8094-d2d126a082df
-- title:
--   PMinkowski Volume Form
-- statement:
--   Definitions and structural lemmas for PMinkowski Volume Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMinkowskiVolumeForm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open Module MeasureTheory Submodule
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]
end GroundTheory.Heights₂.Heights.FiniteCovolume



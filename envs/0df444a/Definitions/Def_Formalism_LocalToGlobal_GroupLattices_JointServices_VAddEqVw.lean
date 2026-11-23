-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_JointServices_VAddEqVw
-- name    : Formalism_LocalToGlobal_GroupLattices_JointServices_VAddEqVw
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:47:29.119093+00:00
-- url     : https://prove2.me/theorems/5a749387-d113-4e3b-803c-e7d87530873e
-- title:
--   VAdd Eq Vw
-- statement:
--   Definitions and structural lemmas for VAdd Eq Vw, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/JointServices/VAddEqVw.lean

import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_NormaliserValuationBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions (vAdd)
open Formalism.DivisionValues (vw)
noncomputable section
namespace Formalism.L2.G.ServJoint
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def VGeq (w : HeightOneSpectrum (𝓞 K)) (s : ℝ) (z : K) : Prop := z = 0 ∨ s ≤ (vAdd w z : ℝ)
end Formalism.L2.G.ServJoint
end



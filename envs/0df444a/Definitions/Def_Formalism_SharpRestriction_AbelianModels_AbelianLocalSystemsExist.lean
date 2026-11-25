-- Prove2me | Definitions.Def_Formalism_SharpRestriction_AbelianModels_AbelianLocalSystemsExist
-- name    : Formalism_SharpRestriction_AbelianModels_AbelianLocalSystemsExist
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T23:54:17.001374+00:00
-- url     : https://prove2.me/theorems/16654172-2a04-49fe-9e60-94a028c5c638
-- title:
--   Abelian Local Systems Exist
-- statement:
--   Definitions and structural lemmas for Abelian Local Systems Exist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AbelianModels/AbelianLocalSystemsExist.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ModelDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ZetaZeros.MainNotions.AbelianModels
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
def AbelianLocalSystemsExist : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), AbelianAtQZero Dw
end ZetaZeros.MainNotions.AbelianModels



-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
-- name    : OAI_Combinatorics_SharpThreshold_Probability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:23:03.664875+00:00
-- url     : https://prove2.me/theorems/bb298dda-a01e-4ac1-9c6c-43373d533b4c
-- title:
--   Elementary facts about the $0/1$ value of a Boolean
-- statement:
--   Let $[b]\in\{0,1\}$ denote the real value of a Boolean $b$ ($[\mathrm{true}]=1$, $[\mathrm{false}]=0$). Then
--   $$
--   0\le[b]\le1,\qquad[b]^2=[b],\qquad[\neg b]=1-[b] .
--   $$
--
--   These identities let probabilities and variances of Boolean functions be computed as expectations of indicators.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/Probability.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/Probability.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SharpThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits

namespace OAI

noncomputable section
namespace Problem313

@[simp] theorem boolReal_nonneg (b : Bool) : 0 ≤ boolReal b := by
  cases b <;> norm_num [boolReal]

@[simp] theorem boolReal_le_one (b : Bool) : boolReal b ≤ 1 := by
  cases b <;> norm_num [boolReal]

@[simp] theorem boolReal_sq (b : Bool) : boolReal b ^ 2 = boolReal b := by
  cases b <;> norm_num [boolReal]

@[simp] theorem boolReal_not (b : Bool) : boolReal (!b) = 1 - boolReal b := by
  cases b <;> norm_num [boolReal]

end Problem313

end

end OAI



-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
-- name    : OAI_Combinatorics_SharpThreshold_BooleanDerivative
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:30:22.180932+00:00
-- url     : https://prove2.me/theorems/c6063593-89b6-4398-b2c4-1baa9e38db2a
-- title:
--   Powers of differences of Booleans
-- statement:
--   For Booleans $a,b$ with real values $[a],[b]\in\{0,1\}$,
--   $$
--   \bigl|[a]-[b]\bigr|=\bigl([a]-[b]\bigr)^2=\bigl([a]-[b]\bigr)^4=[a\ne b] .
--   $$
--
--   For a Boolean function, every $L^q$ norm of a discrete derivative is the probability that the coordinate is pivotal. This identity drives the hypercontractive influence bounds.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BooleanDerivative.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BooleanDerivative.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative

namespace OAI

universe u

noncomputable section
namespace Problem313

@[simp] theorem boolReal_sub_abs (a b : Bool) :
    |boolReal a - boolReal b| = if a ≠ b then 1 else 0 := by
  cases a <;> cases b <;> norm_num [boolReal]

@[simp] theorem boolReal_sub_sq (a b : Bool) :
    (boolReal a - boolReal b) ^ 2 = if a ≠ b then 1 else 0 := by
  cases a <;> cases b <;> norm_num [boolReal]

@[simp] theorem boolReal_sub_fourth (a b : Bool) :
    (boolReal a - boolReal b) ^ 4 = if a ≠ b then 1 else 0 := by
  cases a <;> cases b <;> norm_num [boolReal]

namespace Reindex
variable {ι : Type u} [Fintype ι] [dι : DecidableEq ι]

end Reindex
end Problem313

end

end OAI



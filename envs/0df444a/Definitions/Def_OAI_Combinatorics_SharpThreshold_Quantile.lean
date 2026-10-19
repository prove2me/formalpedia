-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_Quantile
-- name    : OAI_Combinatorics_SharpThreshold_Quantile
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:46:01.536027+00:00
-- url     : https://prove2.me/theorems/c7b48e75-60f9-410d-a83b-0df3e746d499
-- title:
--   Quantile of a function on the unit interval
-- statement:
--   For $\mu:\mathbb{R}\to\mathbb{R}$ and a level $a$,
--   $$
--   q_\mu(a)=\inf\{p\in[0,1]:\ a\le\mu(p)\} .
--   $$
--
--   For $\mu(p)$ the probability that an increasing property holds, $q_\mu(a)$ is the edge density at which the property reaches probability $a$. The threshold width is $q_\mu(1-\varepsilon)-q_\mu(\varepsilon)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/Quantile.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/Quantile.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype
import Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierProjection
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOptionExpectation

namespace OAI

noncomputable section
namespace Problem313

def unitQuantile (μ : ℝ → ℝ) (a : ℝ) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p}

end Problem313

end

end OAI



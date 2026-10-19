-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities
-- name    : OAI_Combinatorics_SharpThreshold_ProjectionIdentities
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:41:08.295014+00:00
-- url     : https://prove2.me/theorems/99aa53a7-4087-41ec-91f1-627cb6d0370b
-- title:
--   Coefficients and synthesis for a weighted basis
-- statement:
--   Let $X$ be finite, $w:X\to\mathbb{R}$ a weight, and $(b_i)_{i\in\iota}$ a family of functions on $X$.
--
--   1. The coefficient of $f$ at $i$ is $\langle f,b_i\rangle_w=\sum_{x}w(x)f(x)b_i(x)$.
--   2. For a finite set $L$ of indices and coefficients $c$, the synthesis is
--   $$
--   \Bigl(\sum_{i\in L}c_ib_i\Bigr)(x)=\sum_{i\in L}c_i\,b_i(x) .
--   $$
--
--   For an orthonormal basis, synthesizing the coefficients over $L$ gives the orthogonal projection onto the span of $\{b_i\}_{i\in L}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/ProjectionIdentities.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/ProjectionIdentities.lean by skeleton subtraction
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

namespace OAI

universe u v

noncomputable section

namespace Problem313.WeightedProjection

open scoped BigOperators

variable {ι : Type u} {X : Type v} [Fintype X]

def coefficient (w : X → ℝ) (basis : ι → X → ℝ) (f : X → ℝ) (i : ι) : ℝ :=
  ∑ x, w x * f x * basis i x

def synthesis (basis : ι → X → ℝ) (L : Finset ι) (c : ι → ℝ) (x : X) : ℝ :=
  ∑ i ∈ L, c i * basis i x

end Problem313.WeightedProjection

end

end OAI



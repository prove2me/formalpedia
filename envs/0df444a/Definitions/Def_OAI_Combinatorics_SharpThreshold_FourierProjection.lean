-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierProjection
-- name    : OAI_Combinatorics_SharpThreshold_FourierProjection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:42:03.245662+00:00
-- url     : https://prove2.me/theorems/2fbd2e22-f64d-4555-a305-2579a765db44
-- title:
--   Projection onto a set of biased Fourier characters
-- statement:
--   Let $\iota$ be a finite set and $0<p<1$. On $\{0,1\}^\iota$ let $w_p(x)=\prod_ip^{[x_i]}(1-p)^{1-[x_i]}$, $\chi_p(b)=([b]-p)/\sqrt{p(1-p)}$, $\chi_S(x)=\prod_{i\in S}\chi_p(x_i)$ and $\hat g(S)=\sum_xw_p(x)g(x)\chi_S(x)$. For a finite family $L$ of subsets of $\iota$, the projection of $g$ onto the characters in $L$ is
--   $$
--   P_Lg(x)=\sum_{S\in L}\hat g(S)\,\chi_S(x) .
--   $$
--
--   Taking $L$ to be the sets of a given size gives the level-$d$ part of $g$. Low levels are where the influence argument concentrates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierProjection.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/FourierProjection.lean by skeleton subtraction
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

namespace OAI

universe u

noncomputable section

namespace Problem313.BiasedFourier

open scoped BigOperators Classical

variable {ι : Type u} [Fintype ι]

/-- The projection onto the specified finite collection of Fourier characters. -/
def project (p : ℝ) (L : Finset (Finset ι))
    (g : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  ∑ S ∈ L, coeff p g S * char p S x

end Problem313.BiasedFourier

end

end OAI



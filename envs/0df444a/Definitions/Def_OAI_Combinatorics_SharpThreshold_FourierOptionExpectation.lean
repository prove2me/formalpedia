-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOptionExpectation
-- name    : OAI_Combinatorics_SharpThreshold_FourierOptionExpectation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:45:13.601988+00:00
-- url     : https://prove2.me/theorems/6491b15d-6cee-41f9-b064-6fd8296bf993
-- title:
--   The biased weight factors off one extra coordinate
-- statement:
--   Let $\iota^+=\iota\sqcup\{\star\}$, and let $w_p$ denote the $p$-biased product weight. For $x\in\{0,1\}^{\iota^+}$ with restriction $x'$ to $\iota$,
--   $$
--   w_p(x)=w_p(x_\star)\,w_p(x') .
--   $$
--   In particular the configuration that equals $b$ at $\star$ and $x'$ on $\iota$ has weight $w_p(b)w_p(x')$.
--
--   Expectations over $\iota^+$ can therefore be computed one coordinate at a time. This underlies induction on the number of coordinates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierOptionExpectation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/FourierOptionExpectation.lean by skeleton subtraction
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

namespace OAI

universe u

noncomputable section

open scoped BigOperators
open Classical

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

/-- Separate the new coordinate from the product Bernoulli weight. -/
theorem weight_option (p : ℝ) (x : Option ι → Bool) :
    weight p x = scalarWeight p (x none) * weight p (fun i => x (some i)) := by
  simp only [weight, Fintype.prod_option]

@[simp] theorem weight_option_elim (p : ℝ) (b : Bool) (x : ι → Bool) :
    weight p ((fun i : Option ι => Option.elim i b x)) = scalarWeight p b * weight p x := by
  rw [weight_option]
  rfl

end Problem313.BiasedFourier

end

end OAI



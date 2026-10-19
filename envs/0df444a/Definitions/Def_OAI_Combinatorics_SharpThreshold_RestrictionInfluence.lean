-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
-- name    : OAI_Combinatorics_SharpThreshold_RestrictionInfluence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:36:36.446906+00:00
-- url     : https://prove2.me/theorems/2f91d077-2d0a-487c-8738-cf20849e41be
-- title:
--   Biased weights, influences and joins on arbitrary coordinates
-- statement:
--   Let $\iota$ be a finite set of coordinates and $p\in\mathbb{R}$. A point of the cube is $x\in\{0,1\}^\iota$, with $p$-biased weight $w_p(x)=\prod_ip^{[x_i]}(1-p)^{1-[x_i]}$.
--
--   1. The pivotal influence of coordinate $i$ on $f:\{0,1\}^\iota\to\{0,1\}$ is
--   $$
--   I_i^p(f)=\sum_xw_p(x)\bigl[f(x^{i\to1})\ne f(x^{i\to0})\bigr],
--   $$
--      where the sum also runs over the redundant value of $x_i$.
--   2. For a predicate $P$ on coordinates, $\mathrm{join}(x,y)$ glues a free configuration $x$ on $\{P\}$ and an exterior one $y$ on $\{\neg P\}$.
--
--   Influences of a restriction are averaged over the exterior configuration. This is how block restrictions inherit influence bounds.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/RestrictionInfluence.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/RestrictionInfluence.lean by skeleton subtraction
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

namespace OAI

universe u

/-! Finite-product averaging for pivotal influences under restrictions. -/
noncomputable section
open scoped BigOperators

namespace Problem313.RestrictionInfluence

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Bernoulli weight on an arbitrary finite set of coordinates. -/
def weight (p : ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, if x i = true then p else 1 - p

/-- The pivotal influence, with the redundant pivotal coordinate included in the sum. -/
def influence (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) : ℝ := by
  classical
  exact ∑ x, if f (Function.update x i true) ≠ f (Function.update x i false)
    then weight p x else 0

variable (P : ι → Prop) [DecidablePred P]

/-- Glue a free and an exterior configuration into a full configuration. -/
def join (x : {i // P i} → Bool) (y : {i // ¬ P i} → Bool) : ι → Bool :=
  fun i => if h : P i then x ⟨i, h⟩ else y ⟨i, h⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem join_pos (x : {i // P i} → Bool) (y : {i // ¬ P i} → Bool)
    (i : {i // P i}) : join P x y i = x i := by
  simp [join, i.property]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem join_neg (x : {i // P i} → Bool) (y : {i // ¬ P i} → Bool)
    (i : {i // ¬ P i}) : join P x y i = y i := by
  simp [join, i.property]

end Problem313.RestrictionInfluence

end

end OAI



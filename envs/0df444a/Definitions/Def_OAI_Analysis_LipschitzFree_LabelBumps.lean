-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps
-- name    : OAI_Analysis_LipschitzFree_LabelBumps
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:20:24.501628+00:00
-- url     : https://prove2.me/theorems/2bac0ee5-f456-490b-adf9-66930b2fc40a
-- title:
--   Tent-shaped bump functions pulled back along a label map
-- statement:
--   Let $M$ and $N$ be metric spaces, $h:M\to N$ a map (in the construction, the label map from a metric block to its box of labels), $a\in N$ a centre, and $L,K\in\mathbb{R}$ the height and the width. The label bump is the function $b=b_{h,a,L,K}:M\to\mathbb{R}$,
--   $$b(t)=L\cdot\max\Bigl(1-\frac{d_N\bigl(a,h(t)\bigr)}{K},\;0\Bigr).$$
--   For $L\ge0$ and $K>0$ this is the tent function of height $L$ and radius $K$ around $a$ in $N$, pulled back along $h$: it equals $L$ at points $t$ with $h(t)=a$, decreases linearly in the distance $d_N(a,h(t))$, and vanishes once $d_N(a,h(t))\ge K$.
--
--   Bumps of this kind are the scalar test functions of the obstruction argument. Centred at the label of a vertex, with height $L$ and width $K$ taken from the block parameters, they are Lipschitz on $M$ with constant $L/K$ whenever $h$ is $1$-Lipschitz, $L\ge0$ and $K>0$, and pairing them with the coefficient vectors of an operator measures how much mass stays at points with nearby labels.
--
--   **Formalization Note** `labelBump h a L K t` is defined for all real $L,K$; for $K=0$ Lean's convention $x/0=0$ makes it the constant function $L$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/LabelBumps.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/LabelBumps.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiscreteLipschitzFree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights

namespace OAI

/-!
# Lipschitz label bumps and affine mass estimates
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M N : Type*} [MetricSpace M] [MetricSpace N]

def labelBump (h : M → N) (a : N) (L K : ℝ) (t : M) : ℝ :=
  L * max (1 - dist a (h t) / K) 0

end DiscreteFree
end

end

end OAI



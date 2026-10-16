-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_LabelBumps__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T12:15:25.922623+00:00
-- url     : https://prove2.me/theorems/9c53a72d-e2d4-4b37-af40-a3f7c8b47e68
-- title:
--   Truncated linear bump functions centred at a label
-- statement:
--   Let $M$ and $N$ be metric spaces, $h:M\to N$ a map (thought of as assigning a label in $N$ to each point of $M$), $a\in N$ a centre, and $L,K$ real numbers. The **label bump** is the real function on $M$
--   $$\beta_{h,a,L,K}(t)=L\cdot\max\Bigl(1-\frac{d_N\bigl(a,h(t)\bigr)}{K},\;0\Bigr),\qquad t\in M .$$
--
--   For $K>0$ and $L\ge0$ this is a truncated cone in the label variable: it equals $L$ at points whose label is $a$, decreases linearly in the label distance $d_N(a,h(t))$, and vanishes once that distance is at least $K$. In particular, if $h$ is $1$-Lipschitz then the bump is Lipschitz with constant $L/K$, so such bumps serve as explicit Lipschitz test functions localised near a prescribed label.
--
--   **Formalization Note** The definition is `labelBump h a L K t` with no hypotheses on $L$ or $K$. If $K=0$, Lean's convention $x/0=0$ makes the quotient vanish, so the bump is the constant function $L$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/LabelBumps.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/LabelBumps.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RealL1Renorming mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Model__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coefficients
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Words__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights__RealL1Renorming

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



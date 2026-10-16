-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_AffineWeights__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T12:13:01.506754+00:00
-- url     : https://prove2.me/theorems/1259679b-d918-42b7-840c-69c77b79f26c
-- title:
--   Affine weights of an element of a Lipschitz-free space on a finite set containing the base point
-- statement:
--   Let $(M,d)$ be a metric space with base point $o$ that is 1-separated ($d(x,y)\ge1$ whenever $x\neq y$), and let $\mathcal{F}(M)$ be its Lipschitz-free space, the closed span of the evaluation functionals $\delta_x$ in the dual of the space of real Lipschitz functions on $M$ vanishing at $o$. For $j\in M$ let $c_j:\mathcal{F}(M)\to\mathbb{R}$ be the coordinate functional given by pairing with the indicator function of $\{j\}$ (taken to be $0$ when $j=o$), so that $c_j(\delta_x)=1$ if $x=j\neq o$ and $0$ otherwise.
--
--   Let $S\subseteq M$ be a finite set with $o\in S$. For $u\in\mathcal{F}(M)$ and $j\in S$ the **affine weight** of $u$ at $j$ is
--   $$\alpha_j(u)=c_j(u)+\begin{cases}1-\displaystyle\sum_{k\in S}c_k(u), & j=o,\\ 0, & j\neq o.\end{cases}$$
--   The file proves that these weights always have total mass one:
--   $$\sum_{j\in S}\alpha_j(u)=1 .$$
--
--   The construction converts the coefficient vector of $u$ on $S$ into a family of signed weights summing to $1$, the base point absorbing the remaining mass. For elements $u$ supported on $S$ (that is, $u=\sum_{j\in S}c_j(u)\,\delta_j$), pairing these weights with the values of a Lipschitz function $g$ on $S$ gives $u(g-g(o))+g(o)$, which is how bounds on $\|u\|$ are turned into bounds on weighted averages of $g$.
--
--   **Formalization Note** The weights are `affineWeights o sep S ho u j` for `j` in the subtype of the finite set `S`, where `sep` is the 1-separation hypothesis and `ho` the membership of the base point; the mass identity is `affineWeights_mass`. Since the coordinate at the base point vanishes, the weight at $o$ equals $1-\sum_{k\in S}c_k(u)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/AffineWeights.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/AffineWeights.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Affine signed coefficients and quantitative pairing bounds
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y) (S : Finset M) (ho : o ∈ S)

def affineWeights (u : FreeSpace o) (j : S) : ℝ :=
  coordinate o sep j.val u +
    if j = ⟨o,ho⟩ then 1 - ∑ k : S, coordinate o sep k.val u else 0

@[simp] theorem affineWeights_mass (u : FreeSpace o) :
    ∑ j : S, affineWeights o sep S ho u j = 1 := by
  simp [affineWeights, Finset.sum_add_distrib]

end DiscreteFree
end

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y) (S : Finset M) (ho : o ∈ S)

end DiscreteFree
end

end

end OAI



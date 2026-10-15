-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
-- name    : OAI_Analysis_LipschitzFree_AffineWeights
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:19:20.994566+00:00
-- url     : https://prove2.me/theorems/78ae554f-265f-4f2c-a148-235f74714122
-- title:
--   Affine coefficient vectors of free-space elements on a finite set containing the base point
-- statement:
--   Let $(M,d)$ be a metric space with base point $o$ that is $1$-separated ($d(x,y)\ge1$ for $x\neq y$), and let $\mathcal{F}(M)$ be its Lipschitz-free space, the closed span of the point evaluations $\delta_x$ in the dual of the space $\mathrm{Lip}_0(M)$ of real Lipschitz functions vanishing at $o$. For $j\in M$ let $c_j:\mathcal{F}(M)\to\mathbb{R}$ be the coordinate functional obtained by pairing with the indicator function of $\{j\}$ (and $c_o=0$), so that $c_j(\delta_x)=1$ if $x=j\neq o$ and $c_j(\delta_x)=0$ otherwise. Fix a finite set $S\subseteq M$ with $o\in S$.
--
--   For $u\in\mathcal{F}(M)$ the affine weight vector $\mu(u)=(\mu_j(u))_{j\in S}$ is
--   $$\mu_j(u)=c_j(u)+[\,j=o\,]\Bigl(1-\sum_{k\in S}c_k(u)\Bigr),$$
--   where $[\,j=o\,]$ is $1$ if $j=o$ and $0$ otherwise; thus $\mu_j(u)=c_j(u)$ for $j\in S\setminus\{o\}$ and $\mu_o(u)=1-\sum_{k\in S}c_k(u)$. These weights always have total mass one:
--   $$\sum_{j\in S}\mu_j(u)=1 .$$
--
--   For $u=\delta_x$ with $x\in S$ the vector $\mu(u)$ is the unit point mass at $x$. In general $\mu(u)$ records the coordinates of $u$ on $S$ and places the remaining mass at the base point, where $\delta_o=0$. Because the mass is one, such weight vectors can be paired with functions on $S$ that do not vanish at $o$: for $u$ in the span of $\{\delta_j: j\in S\}$ and a Lipschitz function $g$ on $M$, the pairing $\sum_{j\in S}\mu_j(u)\,g(j)$ equals $\langle u,\,g-g(o)\rangle+g(o)$. This is how bump functions of labels are tested against the images $T\delta_x$ of an operator $T$.
--
--   **Formalization Note** `affineWeights o sep S ho u` is a function on the elements of the `Finset` `S` (as a subtype), where `ho : o ∈ S` and `sep` is the separation hypothesis; the term $[\,j=o\,]$ is an `if`. `affineWeights_mass` is the mass identity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/AffineWeights.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/AffineWeights.lean by skeleton subtraction
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



-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Selection
-- name    : OAI_Analysis_C0Absorption_Selection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:07:24.921987+00:00
-- url     : https://prove2.me/theorems/22510c58-fd45-405c-bfc0-da7bb965651a
-- title:
--   Tag localization of cylinder bases
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. $c_0$ is the Banach space of real sequences tending to zero with the sup norm, $B$ is its closed unit ball, and for a finite set $I$ of coordinates the cube $[-1,1]^I$ is the image of $B$ under restriction to $I$. A family of cylinder bases provides coordinate sets $I_\gamma$, bands $j_\gamma$, band lengths $\ell_j$ and base functions.
--
--   A tag localization assigns to each index $\gamma$ a tag $t_\gamma\in[-1,1]^{\mathbb N}$ such that:
--
--   1. every coordinate set contains the prefix $\{0,\dots,j_\gamma-1\}$;
--   2. $\ell_j\to0$ as $j\to\infty$;
--   3. on the support of each base function, the first $j_\gamma$ coordinates stay close to the tag:
--   $$
--   |x_k-t_\gamma(k)|\le2\cdot2^{-j_\gamma}\qquad(k<j_\gamma).
--   $$
--
--   So each base function lives in a small cylinder around its tag, of width comparable to its band.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Selection.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Selection.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the C0Absorption mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

structure TagLocalization {Γ : Type*} (B : CylinderBases Γ) where
  tag : Γ → ℕ → Icc (-1 : ℝ) 1
  contains_prefix : ∀ γ, Finset.range (B.band γ) ⊆ B.coordinates γ
  ell_tendsto : Tendsto B.ell atTop (nhds 0)
  base_support : ∀ γ (k : B.coordinates γ), k.val < B.band γ →
    ∀ x ∈ tsupport (B.base γ), dist (x k) (tag γ k.val) ≤ 2*dyadic (B.band γ)

namespace TagLocalization
variable {Γ : Type*} {B : CylinderBases Γ} (loc : TagLocalization B)

end TagLocalization

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

end OAI



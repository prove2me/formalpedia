-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Onto
-- name    : OAI_Analysis_C0Absorption_Onto
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:49:45.232476+00:00
-- url     : https://prove2.me/theorems/02488f7b-8e03-4df3-b40b-d737aba91eb8
-- title:
--   Finite targets and square truncations of label sequences
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. Levels are pairs $(i,n)$, labels are (level, band, grid tag), and the coordinates of $c_0$ are split into row coordinates indexed by $\mathbb N$ and label coordinates indexed by labels. For $y\in C_0(\mathrm{Labels})$:
--
--   1. **Finite target.** $\mathrm{finiteTarget}_N(y)$ is the vector in the finite coordinate block $F_N$ whose row coordinates are $0$ and whose label coordinates are $y_\gamma$, for the labels of the levels $(i,n)$ with $i,n\le N$.
--   2. **Square truncation.**
--   $$
--   \mathrm{blockSquare}_N(y)_\gamma=\begin{cases}y_\gamma,&\gamma\text{ has level }(i,n)\text{ with }i,n\le N,\\0,&\text{otherwise}.\end{cases}
--   $$
--   It is again in $C_0(\mathrm{Labels})$, and $\mathrm{blockSquare}_N(y)\to y$ as $N\to\infty$.
--
--   These are used to solve the shift equation level by level in finite blocks and pass to the limit.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Onto.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Onto.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations
import Definitions.Def_OAI_Analysis_C0Absorption_Detection
import Definitions.Def_OAI_Analysis_C0Absorption_Grid
import Definitions.Def_OAI_Analysis_C0Absorption_Weights
import Definitions.Def_OAI_Analysis_C0Absorption_Angles
import Definitions.Def_OAI_Analysis_C0Absorption_Blocks
import Definitions.Def_OAI_Analysis_C0Absorption_Correction
import Definitions.Def_OAI_Analysis_C0Absorption_Frozen
import Definitions.Def_OAI_Analysis_C0Absorption_Tags
import Definitions.Def_OAI_Analysis_C0Absorption_Operators
import Definitions.Def_OAI_Analysis_C0Absorption_Shift
import Definitions.Def_OAI_Analysis_C0Absorption_Space
import Definitions.Def_OAI_Analysis_C0Absorption_Finite
import Definitions.Def_OAI_Analysis_C0Absorption_FiniteShift

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

variable {N : ℕ}

def finiteTarget (N : ℕ) (y : BlockC0) : FInput N := Sum.elim (fun _ => 0) (fun γ => y (fLabel γ))

def blockSquare (N : ℕ) (y : BlockC0) : BlockC0 :=
  cfunOfTendsto (fun γ => if γ.level.1≤N ∧ γ.level.2≤N then y γ else 0)
    ((cfun_tendsto y).if' tendsto_const_nhds)

@[simp] theorem blockSquare_apply (N : ℕ) (y : BlockC0) (γ : Label) :
    blockSquare N y γ=if γ.level.1≤N ∧ γ.level.2≤N then y γ else 0 := rfl

end
end C0Absorption

end OAI



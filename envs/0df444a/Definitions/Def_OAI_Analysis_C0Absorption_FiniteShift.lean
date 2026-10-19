-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_FiniteShift
-- name    : OAI_Analysis_C0Absorption_FiniteShift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:48:01.701549+00:00
-- url     : https://prove2.me/theorems/b1d3373e-94ab-4d0e-a642-dbc5cfc988ad
-- title:
--   The recomputed finite shift
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. For each $N$ there is a finite coordinate block $F_N$, consisting of $N+1$ row coordinates and the labels of the levels $(i,n)$ with $i,n\le N$, isometrically embedded into $c_0$. On it, every frozen weight system $W$ gives an invertible linear map $\Phi_{N,W}$.
--
--   The recomputed finite shift evaluates the frozen map with the state weights of the normalized embedded point:
--   $$
--   \mathrm{finiteRecomputed}_N(x)=\Phi_{N,W(e/\|e\|)}(x),\qquad e=\mathrm{embed}_N(x).
--   $$
--   It is a nonlinear, positively homogeneous map of the finite-dimensional space with $\mathrm{finiteRecomputed}_N(0)=0$. It approximates the recomputed shift on $c_0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/FiniteShift.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/FiniteShift.lean by skeleton subtraction
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

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

variable {N : ℕ}

def finiteRecomputed (N : ℕ) (x : FInput N) : FInput N :=
  finiteFrozen N (stateWeights (normalizedBall (finiteEmbed N x))) x

@[simp] theorem finiteRecomputed_zero (N : ℕ) : finiteRecomputed N 0=0 := map_zero _

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators

section FiniteOperators
variable {A : Type*} [Fintype A] [DecidableEq A] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end FiniteOperators

end
end C0Absorption

end OAI



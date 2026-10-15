-- Prove2me | Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
-- name    : OAI_Combinatorics_BooleanFunctions_Blocks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:20:47.821072+00:00
-- url     : https://prove2.me/theorems/9d0cf62c-c21e-48a0-88c7-fca4145a72ca
-- title:
--   Currying the cube on a product index set into blocks
-- statement:
--   For types $K$, $I$ and $\Lambda$, the file defines the currying bijection
--   $$\mathrm{curry}:\Lambda^{K\times I}\to\big(\Lambda^{I}\big)^{K},\qquad \mathrm{curry}(x)_j(i)=x(j,i),$$
--   whose inverse sends a family $(y_j)_{j\in K}$ of functions on $I$ to the function $(j,i)\mapsto y_j(i)$ on $K\times I$.
--
--   With $\Lambda=\mathbb{B}=\{\mathrm{false},\mathrm{true}\}$ it identifies the Boolean cube on the coordinate set $K\times I$ with $K$ copies (blocks) of the cube $\mathbb{B}^I$; the $j$-th block of $x$ is the point $x_{j,\cdot}=(x(j,i))_{i\in I}$. Because it is a bijection, uniform averages over the two sides agree, and under the uniform distribution the blocks are independent. This is what allows an observation to be run separately on the disjoint blocks of a larger cube, as in the grouped and switched observations of later files.
--
--   **Formalization Note** `blockCurry κ ι α` is an `Equiv` between `(κ × ι) → α` and `κ → ι → α`; both inverse laws hold by `rfl`. The file enables classical decidability locally and contains no other declarations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Blocks.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Blocks.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SquareRootDegree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning

namespace OAI

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-! ## Disjoint blocks and finite observation degree calculus -/

attribute [local instance] Classical.propDecidable

def blockCurry (κ ι α : Type*) : ((κ × ι) → α) ≃ (κ → ι → α) where
  toFun x j i := x (j,i)
  invFun x ji := x ji.1 ji.2
  left_inv _ := rfl
  right_inv _ := rfl

end SquareRootDegree

end

end OAI



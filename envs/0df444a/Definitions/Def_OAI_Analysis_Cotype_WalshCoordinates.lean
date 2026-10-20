-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
-- name    : OAI_Analysis_Cotype_WalshCoordinates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:31:45.804032+00:00
-- url     : https://prove2.me/theorems/c4bc7e0e-696f-461e-b536-2a1b9db883f6
-- title:
--   Splitting the cube into two blocks
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections.
--
--   1. **Cube join.** The bijection
--   $$
--   \{0,1\}^n\times\{0,1\}^j\to\{0,1\}^{n+j},\qquad(a,b)\mapsto a\,b ,
--   $$
--   which appends coordinates, with inverse taking the first $n$ and the last $j$ coordinates. It identifies Walsh characters on the larger cube with products of characters on the two blocks, which is used to tensorize Walsh estimates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/WalshCoordinates.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/WalshCoordinates.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def cubeJoin (n j : ℕ) : Cube n × Cube j ≃ Cube (n+j) where
  toFun p := Fin.append p.1 p.2
  invFun u := (fun i => u (Fin.castAdd j i), fun i => u (Fin.natAdd n i))
  left_inv p := by ext i <;> simp
  right_inv u := by ext i; exact Fin.addCases (by simp) (by simp) i

@[simp] theorem cubeJoin_apply {n j : ℕ} (a : Cube n) (b : Cube j) :
    cubeJoin n j (a,b) = Fin.append a b := rfl

end Cotype

end

end OAI



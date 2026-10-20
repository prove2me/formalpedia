-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_WalshNorm
-- name    : OAI_Analysis_Cotype_WalshNorm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:30:10.69615+00:00
-- url     : https://prove2.me/theorems/13aed9f1-9f49-46d6-8c41-c247c57410ac
-- title:
--   Walsh norms of operators
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. The cube $\{0,1\}^n$ (Booleans) carries the uniform average $\mathbb E$, the signs $\varepsilon_i=\pm1$, the Walsh characters $w_A(\varepsilon)=\prod_{i\in A}\varepsilon_i$, and the norm $\|f\|_{L_2}=(\mathbb E\|f(\varepsilon)\|^2)^{1/2}$ for $X$-valued functions. Let $T:X\to Y$ be bounded.
--
--   1. **Walsh outputs.** The values $\|\widehat{Tf}\|_{L_2}$ over $f:\{0,1\}^n\to X$ with $\|f\|_{L_2}\le1$.
--   2. **Walsh norm.**
--   $$
--   \mathcal W_n(T)=\sup\bigl\{\|\widehat{Tf}\|_{L_2}:\ \|f\|_{L_2(X)}\le1\bigr\},
--   $$
--   the norm of the operator-valued Walsh transform on dimension $n$. It is Lipschitz in $T$, and its decay for the identity operator is the quantitative input of the main argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/WalshNorm.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/WalshNorm.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def walshOutputs (n : ℕ) (T : X →L[ℝ] Y) : Set ℝ :=
  {r | ∃ f : Cube n → X, cubeL2 X f ≤ 1 ∧ cubeL2 Y (operatorWalsh T f) = r}

def walshNorm (n : ℕ) (T : X →L[ℝ] Y) : ℝ := sSup (walshOutputs n T)

end Cotype

end

end OAI



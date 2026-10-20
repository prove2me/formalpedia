-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_WalshDuality
-- name    : OAI_Analysis_Cotype_WalshDuality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:33:03.015566+00:00
-- url     : https://prove2.me/theorems/f0051b1f-c9ff-48a0-b713-4b40c90441df
-- title:
--   Dual pairings for Walsh transforms
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. The cube $\{0,1\}^n$ (Booleans) carries the uniform average $\mathbb E$, the signs $\varepsilon_i=\pm1$, the Walsh characters $w_A(\varepsilon)=\prod_{i\in A}\varepsilon_i$, and the norm $\|f\|_{L_2}=(\mathbb E\|f(\varepsilon)\|^2)^{1/2}$ for $X$-valued functions. Let $T:X\to Y$ be bounded.
--
--   1. **Dual pairing.** For $f:\{0,1\}^n\to X$ and $g:\{0,1\}^n\to X^*$, $\langle f,g\rangle=\mathbb E_u\,g(u)(f(u))$.
--   2. **Walsh bilinear form.**
--   $$
--   B_T(f,g)=\mathbb E_u\,\mathbb E_v\,w_v(u)\,g(v)\bigl(T(f(u))\bigr),
--   $$
--   the pairing of the Walsh transform of $Tf$ with $g$. Norms of Walsh transforms are computed by norming dual functions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/WalshDuality.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/WalshDuality.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def dualPairing {n : ℕ} (f : Cube n → X) (g : Cube n → (X →L[ℝ] ℝ)) : ℝ :=
  average (fun u => g u (f u))

def walshBilinear {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X)
    (g : Cube n → (Y →L[ℝ] ℝ)) : ℝ :=
  average (fun u => average (fun v => character v u * g v (T (f u))))

end Cotype

end

end OAI



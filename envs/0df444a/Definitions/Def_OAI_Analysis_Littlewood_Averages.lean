-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_Averages
-- name    : OAI_Analysis_Littlewood_Averages
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:08:07.242879+00:00
-- url     : https://prove2.me/theorems/5f876fa5-ac85-451c-9f1a-aef9c6966e79
-- title:
--   Uniform average of a real function on a finite set
-- statement:
--   For a finite type $\Omega$ and a function $f:\Omega\to\mathbb{R}$, the average of $f$ is
--   $$
--   \operatorname{avg}(f)=\frac{1}{|\Omega|}\sum_{\omega\in\Omega}f(\omega),
--   $$
--   which for nonempty $\Omega$ is the expectation of $f$ under the uniform probability measure on $\Omega$.
--
--   This is the probabilistic language of the combinatorial packing argument modulo a prime $q$: averages are taken over random choices of a shift and a sign in each chunk, over the points of $(\mathbb{Z}/q\mathbb{Z})^m$, and over the fibers of linear functionals. Linearity, monotonicity, exchange of averages over product sets and Chebyshev-type bounds for it, together with the existence of a point where $f$ is at most its average, turn second-moment estimates into the existence of good configurations.
--
--   **Formalization Note** `avg f` is `(∑ ω, f ω) / Fintype.card Ω`. The section declares `[Fintype Ω] [Nonempty Ω]`, but the formula only uses finiteness; on an empty type it evaluates to $0$ by the convention $x/0=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Averages.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Averages.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AsymptoticallyMinimalLittlewood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble

namespace OAI

universe uΩ uI uΛ uK uA uJ uY

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

section Average
variable {Ω : Type uΩ} [Fintype Ω] [Nonempty Ω]

def avg (f : Ω → ℝ) : ℝ := (∑ ω, f ω)/(Fintype.card Ω)

end Average
end
end Packing
end AsymptoticallyMinimalLittlewood

end OAI



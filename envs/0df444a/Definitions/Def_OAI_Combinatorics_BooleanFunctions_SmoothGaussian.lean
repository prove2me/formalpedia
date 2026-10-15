-- Prove2me | Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
-- name    : OAI_Combinatorics_BooleanFunctions_SmoothGaussian
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:25:58.266845+00:00
-- url     : https://prove2.me/theorems/8f6516aa-4cbf-4498-a8b1-8d9f8407663e
-- title:
--   Tent functions and the weighted mass, mean and variance of a measure on the line
-- statement:
--   1. **Tent function.** For $a,h,x\in\mathbb{R}$,
--   $$\operatorname{tent}_{a,h}(x)=\max\Big\{0,\;1-\frac{|x-a|}{h}\Big\}.$$
--   For $h>0$ this is the continuous triangular bump of height $1$ at $a$ that vanishes outside the open interval $(a-h,a+h)$. The file records that $\operatorname{tent}_{a,h}$ is continuous for all $a,h$.
--   2. **Weighted mass, mean and variance.** For a measure $\mu$ on $\mathbb{R}$ and a weight $w:\mathbb{R}\to\mathbb{R}$,
--   $$\operatorname{mass}_\mu(w)=\int w\,d\mu,\qquad \operatorname{mean}_\mu(w)=\frac{\int w(x)\,x\,d\mu(x)}{\operatorname{mass}_\mu(w)},\qquad \operatorname{var}_\mu(w)=\frac{\int w(x)\,x^2\,d\mu(x)}{\operatorname{mass}_\mu(w)}-\operatorname{mean}_\mu(w)^2 .$$
--   When $w\ge0$ is integrable (together with $w(x)x$ and $w(x)x^2$) and has positive mass, these are the total mass of $w\,d\mu$ and the mean and variance of the probability measure $w\,d\mu/\operatorname{mass}_\mu(w)$.
--
--   In the project $\mu$ is the standard Gaussian measure and $w$ is a tent: $\operatorname{tent}_{a,h}(x)$ is read as the probability that a value $x$ passes a rare interval test around $a$. Being continuous with compact support, such tests pass through convergence in distribution, and they are later rounded to deterministic tests on finite alphabets.
--
--   **Formalization Note** `tent a h x` is `max 0 (1 - |x-a| / h)`. `mass`, `mean` and `variance` use the Bochner integral, which is $0$ for non-integrable functions, and division by $0$ gives $0$. `continuous_tent` is registered for `fun_prop`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/SmoothGaussian.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/SmoothGaussian.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SquareRootDegree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace SmoothGaussian

/-- A continuous probability of passing a rare interval test. It vanishes
outside the interval, and is rounded to deterministic tests on each finite
input alphabet before constructing any final observation. -/
def tent (a h x : ℝ) : ℝ := max 0 (1 - |x-a| / h)

@[fun_prop] theorem continuous_tent (a h : ℝ) : Continuous (tent a h) := by
  unfold tent
  fun_prop

def mass (μ : Measure ℝ) (w : ℝ → ℝ) : ℝ := ∫ x, w x ∂μ

def mean (μ : Measure ℝ) (w : ℝ → ℝ) : ℝ := (∫ x, w x * x ∂μ) / mass μ w

def variance (μ : Measure ℝ) (w : ℝ → ℝ) : ℝ :=
  (∫ x, w x * x^2 ∂μ) / mass μ w - mean μ w ^ 2

end SmoothGaussian
end SquareRootDegree

end

end OAI



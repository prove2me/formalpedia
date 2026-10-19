-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy
-- name    : OAI_Analysis_Littlewood_SamplingEnergy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:23:40.260215+00:00
-- url     : https://prove2.me/theorems/6cb62b1c-865f-4c99-9926-272fe1b9c514
-- title:
--   Normalized finite quadratic exponential sums sampled from an amplitude
-- statement:
--   Let $e(\theta)=e^{2\pi i\theta}$, let $g:\mathbb{R}\to\mathbb{C}$ be an amplitude, $N\in\mathbb{N}$, and $\beta,b\in\mathbb{R}$. The **finite average** is
--   $$
--   A_N(g;\beta,b)=\frac1N\sum_{k=0}^{N-1}g\Bigl(\frac kN\Bigr)\,e\Bigl(\frac{\beta k^2}{2N}+bk\Bigr),
--   $$
--   with the convention $A_0(g;\beta,b)=0$.
--
--   These averages are the matrix entries of the mean square of a superposition of sampled chirps: expanding $\frac1N\sum_k\bigl|\sum_i c_i\,g_i(k/N)\,e(\lambda_i k^2/(2N)+b_i k)\bigr|^2$ produces the terms $A_N(g_i\overline{g_j};\lambda_i-\lambda_j,b_i-b_j)$. For a smooth bounded $g$ with compact support in $(0,1)$, $A_N(g;\beta,b)\to0$ as $N\to\infty$ whenever $\beta\ne0$ or $b\notin\mathbb{Z}$, while $A_N(g;0,0)\to\int_{\mathbb{R}}g(x)\,dx$; so off-diagonal terms disappear in the limit and diagonal terms converge to $\int|g_i|^2$.
--
--   **Formalization Note** `finiteAverage g N β b` is `(1/(N : ℂ)) * ∑ k : Fin N, g (k/N) * phase (β/N) (-b) k` with `phase t u x` $=e(tx^2/2-ux)$; for $N=0$ the factor $1/0$ is $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SamplingEnergy.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/SamplingEnergy.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

def finiteAverage (g : ℝ → ℂ) (N : ℕ) (β b : ℝ) : ℂ :=
  (1/(N : ℂ))*∑ k : Fin N, g ((k : ℝ)/N)*phase (β/N) (-b) k

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI



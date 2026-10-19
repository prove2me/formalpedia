-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
-- name    : OAI_Analysis_TriangularHilbert_GaussianMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:08:05.602994+00:00
-- url     : https://prove2.me/theorems/d6efb4bb-32df-4963-a1de-b27cc5c39b0f
-- title:
--   Cubic polynomials in one real variable
-- statement:
--   Gaussian moment computations in the heat-flow analysis of the triangular Hilbert transform repeatedly integrate polynomials of degree at most three against Gaussian densities.
--
--   For real coefficients $c_0,c_1,c_2,c_3$ and $x\in\mathbb R$, the cubic polynomial is
--   $$
--   \mathrm{cubic}(c_0,c_1,c_2,c_3,x)=c_0+c_1x+c_2x^2+c_3x^3 .
--   $$
--   Its Gaussian integrals are explicit in terms of the moments $\int x^k\phi_\sigma(x-p)\,dx$ for $k\le3$, which is what makes the third-order scores of the heat flow computable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/GaussianMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/GaussianMoments.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
open scoped NNReal
noncomputable section

def cubic (c0 c1 c2 c3 x : ℝ) : ℝ := c0+c1*x+c2*x^2+c3*x^3

end
end TriangularHilbert.Heat
end

end OAI



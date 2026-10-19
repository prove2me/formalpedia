-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
-- name    : OAI_Analysis_TriangularHilbert_GaussianDom
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:23:43.859474+00:00
-- url     : https://prove2.me/theorems/fcfcf086-e958-47d6-b555-0daf0eaf1c54
-- title:
--   Planar Gaussian and polynomial weights
-- statement:
--   Two auxiliary functions on the plane are used to dominate integrands of the heat flow uniformly.
--
--   1. **Planar Gaussian.** For $b\in\mathbb R$ and $z=(z_1,z_2)$,
--   $$
--   \mathrm{planeGaussian}(b,z)=e^{-b(z_1^2+z_2^2)} .
--   $$
--   2. **Polynomial weight.** $\mathrm{planePoly}(z)=(1+z_1^2)(1+z_2^2)$.
--
--   For $b>0$, the product of a polynomial weight and a planar Gaussian is integrable. This is the dominating function in integrability and differentiation-under-the-integral arguments for heat energies.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/GaussianDom.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/GaussianDom.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert

namespace OAI

section

namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

def planeGaussian (b : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.exp (-b*(z.1^2 + z.2^2))

def planePoly (z : ℝ × ℝ) : ℝ := (1+z.1^2) * (1+z.2^2)

end
end TriangularHilbert.Heat
end

end OAI



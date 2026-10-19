-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_SmoothFormula
-- name    : OAI_Analysis_TriangularHilbert_SmoothFormula
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:45:18.266774+00:00
-- url     : https://prove2.me/theorems/8ac701a3-6749-4bca-bddc-9b9c1cacb878
-- title:
--   Scale primitive and profile of the smooth Hilbert kernel
-- statement:
--   The signed kernel at scale $s$ is $\kappa_s(t)=\frac{t^3/27-ts/3}{s\sqrt s}\phi_{3s}(t)$, where $\phi_\sigma$ is the centred Gaussian density of variance $\sigma$.
--
--   1. **Scale primitive.** $\mathrm{scalePrimitive}(s,t)=\dfrac{2\sqrt s\,\bigl(\frac{t^2}{9s}-\frac13\bigr)\phi_{3s}(t)}{t}$, whose derivative in $s$ is $\kappa_s(t)/s$ for $t\ne0$.
--   2. **Kernel constant.** $\kappa_0=-\frac23\phi_3(0)\ne0$.
--   3. **Profile.**
--   $$
--   \mathrm{kernelProfile}(v)=\kappa_0-2\Bigl(\frac{v^2}9-\frac13\Bigr)\phi_3(v).
--   $$
--   With these, $\int_a^b\kappa_s(t)\frac{ds}s=\dfrac{\mathrm{kernelProfile}(t/\sqrt a)-\mathrm{kernelProfile}(t/\sqrt b)}t$, so the smooth kernel is a smoothed version of $\kappa_0\,\mathbf 1_{\sqrt a<|t|\le\sqrt b}/t$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/SmoothFormula.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/SmoothFormula.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedCenter
import Definitions.Def_OAI_Analysis_TriangularHilbert_SelectedScale
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscretePairing

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

def scalePrimitive (s t : ℝ) : ℝ :=
  2*(Real.sqrt s*((t^2/9)/s-1/3))*density (3*s) t/t

def kernelConstant : ℝ := -(2/3)*density 3 0

def kernelProfile (v : ℝ) : ℝ := kernelConstant-2*(v^2/9-1/3)*density 3 v

lemma kernelConstant_ne_zero : kernelConstant ≠ 0 := by
  unfold kernelConstant
  exact mul_ne_zero (by norm_num) (density_pos (by norm_num) 0).ne'

end
end TriangularHilbert.Heat
end

end OAI



-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_HardPairing
-- name    : OAI_Analysis_TriangularHilbert_HardPairing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:51:37.604283+00:00
-- url     : https://prove2.me/theorems/645bc4d2-753a-41d1-b3ed-8c7bcd4fa989
-- title:
--   The sharply truncated Hilbert kernel and its pairing constant
-- statement:
--   For $0<r<R$ and $t\in\mathbb R$, the hard (sharply truncated) kernel is
--   $$
--   \mathrm{hardKernel}(r,R,t)=\frac{\mathbf 1_{r<|t|}-\mathbf 1_{R<|t|}}t=\frac{\mathbf 1_{r<|t|\le R}}t ,
--   $$
--   the kernel of the Hilbert transform truncated to $r<|t|\le R$.
--
--   The hard pairing constant is
--   $$
--   C_{\mathrm{hard}}=\frac{C_{\mathrm{sel}}+2\,C_{\mathrm{err}}}{|\kappa_0|}>0,
--   $$
--   combining the selected-sum constant and the error pairing constant and dividing by the nonzero kernel constant $\kappa_0=-\frac23\phi_3(0)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/HardPairing.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/HardPairing.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_SmoothFormula
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorEnvelope
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorPairing

namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

def hardKernel (r R t : ℝ) : ℝ :=
  ((if r < |t| then 1 else 0)-(if R < |t| then 1 else 0))/t

def hardPairingConstant : ℝ := (selectedConstant+2*errorPairingConstant)/|kernelConstant|
lemma hardPairingConstant_pos : 0 < hardPairingConstant := by
  unfold hardPairingConstant
  exact div_pos (add_pos selectedConstant_pos (mul_pos (by norm_num) errorPairingConstant_pos)) (abs_pos.mpr kernelConstant_ne_zero)

end
end TriangularHilbert.Heat
end

end OAI



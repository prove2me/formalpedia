-- Prove2me | Definitions.Def_OAI_Analysis_BackwardIntertwiners_ErgodicTransitivity
-- name    : OAI_Analysis_BackwardIntertwiners_ErgodicTransitivity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:04:09.74312+00:00
-- url     : https://prove2.me/theorems/dd7bb86a-7029-4d06-bdf9-c33933d812eb
-- title:
--   Matrix units and coordinate maps between scalar and vector-valued $L^2$ over $\mathbb{Z}_2$
-- statement:
--   This file introduces elementary operators linking the fiber space, the scalar $L^2$ space and the global $L^2$ space of the model. Let $\mathcal{F}=\ell^2(\mathbb{Z})$ be the Hilbert space of square-summable two-sided complex sequences with standard basis $(e_j)_{j\in\mathbb{Z}}$, let $\mu$ be the completed normalized Haar measure on the 2-adic integers $\mathbb{Z}_2$, and let $\mathcal{H}=L^2(\mathbb{Z}_2,\mu;\mathcal{F})$.
--
--   1. **Matrix units.** For $i,j\in\mathbb{Z}$, $E_{ij}v=v_j\,e_i$; this is the rank-one operator on $\mathcal{F}$ sending $e_j$ to $e_i$ and the other basis vectors to $0$.
--   2. **Scalar Hilbert space.** $\mathcal{K}=L^2(\mathbb{Z}_2,\mu;\mathbb{C})$.
--   3. **Coordinate maps.** $\pi_j:\mathcal{H}\to\mathcal{K}$, $(\pi_jf)(x)=f(x)_j$ for almost every $x$.
--   4. **Coordinate embeddings.** $\iota_j:\mathcal{K}\to\mathcal{H}$, $(\iota_jg)(x)=g(x)\,e_j$ for almost every $x$.
--
--   Both $\pi_j$ and $\iota_j$ are bounded linear maps, and $\iota_j$ is a right inverse of $\pi_j$:
--   $$\pi_j\circ\iota_j=\mathrm{id}_{\mathcal{K}}\qquad(j\in\mathbb{Z}).$$
--
--   The module containing these definitions proves the ergodic transitivity theorem: a closed subspace of $\mathcal{H}$ invariant under the forward operator, the backward operator and all multiplications by bounded scalar functions is $\{0\}$ or $\mathcal{H}$. The maps defined here are used for the structural properties of the model: finite combinations of the matrix units $E_{j+1,j}$ approximate each fiber shift in norm, which shows that the fiber operators are compact, and the pair $\pi_j,\iota_j$ transfers infinite dimensionality from $\mathcal{K}$ to $\mathcal{H}$ and describes the coordinate projection $\iota_0\pi_0$.
--
--   **Formalization Note** The names are `rankOneCoordinate i j`, `ScalarHilbert := Lp ℂ 2 baseMeasure`, `coordinateL2 j` and `singleL2 j`; the last two are obtained by composing with a fixed continuous linear map on the values (`ContinuousLinearMap.compLpL`). The almost-everywhere descriptions are `coordinateL2_ae` and `singleL2_ae`, and the right-inverse identity is `coordinateL2_singleL2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/ErgodicTransitivity.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/ErgodicTransitivity.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BackwardIntertwiners mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_HaarBase
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberMaps
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_BackwardWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_GlobalOperators

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

section Localization
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [finiteMeasure : IsFiniteMeasure μ]

end Localization

def rankOneCoordinate (i j : ℤ) : Fiber →L[ℂ] Fiber :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 i).comp (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j)
@[simp] lemma rankOneCoordinate_apply (i j : ℤ) (v : Fiber) :
    rankOneCoordinate i j v = lp.single 2 i (v j) := rfl
abbrev ScalarHilbert := Lp ℂ 2 baseMeasure

def coordinateL2 (j : ℤ) : GlobalHilbert →L[ℂ] ScalarHilbert :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).compLpL 2 baseMeasure

def singleL2 (j : ℤ) : ScalarHilbert →L[ℂ] GlobalHilbert :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 j).compLpL 2 baseMeasure

lemma coordinateL2_ae (j : ℤ) (f : GlobalHilbert) :
    coordinateL2 j f =ᵐ[baseMeasure] fun x => f x j :=
  ContinuousLinearMap.coeFn_compLpL _ _
lemma singleL2_ae (j : ℤ) (f : ScalarHilbert) :
    singleL2 j f =ᵐ[baseMeasure] fun x => lp.single 2 j (f x) :=
  ContinuousLinearMap.coeFn_compLpL _ _
lemma coordinateL2_singleL2 (j : ℤ) (f : ScalarHilbert) :
    coordinateL2 j (singleL2 j f) = f := by
  apply Lp.ext
  filter_upwards [coordinateL2_ae j (singleL2 j f), singleL2_ae j f] with x h₁ h₂
  simp only [h₁, h₂, lp.single_apply_self]

end
end BackwardIntertwiners

end OAI



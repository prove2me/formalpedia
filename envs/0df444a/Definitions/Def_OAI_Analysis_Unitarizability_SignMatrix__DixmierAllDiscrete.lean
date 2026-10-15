-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_SignMatrix__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:23:26.260979+00:00
-- url     : https://prove2.me/theorems/015de4f5-4a21-41ba-b088-11f7dd73156d
-- title:
--   Normalized sign-matrix columns, synthesis along injective selections and bilinear test coefficients
-- statement:
--   Let $I$, $J$ and $K$ be finite sets, where $I$ indexes labels (columns) and $K$ indexes coordinates (rows), and let $\mathbb{R}^K$ and $\mathbb{R}^J$ carry their standard inner products. A sign matrix is a function $\sigma:K\times I\to\{\mathrm{true},\mathrm{false}\}$, and $\varepsilon(\mathrm{true})=1$, $\varepsilon(\mathrm{false})=-1$.
--
--   1. **Zero extension along an embedding.** For an injective map $e:J\to I$ and $z:J\to\mathbb{R}$, the function $\tilde z:I\to\mathbb{R}$ with $\tilde z(e(j))=z_j$ and $\tilde z(i)=0$ for $i\notin e(J)$ (the first identity is recorded as a lemma).
--   2. **Normalized columns.** For $i\in I$, the vector $u^\sigma_i\in\mathbb{R}^K$ with
--   $$(u^\sigma_i)_a=\frac{\varepsilon(\sigma(a,i))}{\sqrt{|K|}}\qquad(a\in K).$$
--   3. **Synthesis along a selection.** For an injective $e:J\to I$, the linear map $\Phi^\sigma_e:\mathbb{R}^J\to\mathbb{R}^K$, $\Phi^\sigma_ez=\sum_{j\in J}z_j\,u^\sigma_{e(j)}$ (recorded as a lemma).
--   4. **Test coefficients.** For an injective $e:J\to I$, $w\in\mathbb{R}^K$ and $z\in\mathbb{R}^J$, the array
--   $$c_{e,w,z}(a,i)=\frac{w_a\,\tilde z(i)}{\sqrt{|K|}}\qquad\bigl((a,i)\in K\times I\bigr).$$
--
--   These definitions linearize a random-matrix estimate: $\langle\Phi^\sigma_ez,w\rangle=\sum_{(a,i)\in K\times I}c_{e,w,z}(a,i)\,\varepsilon(\sigma(a,i))$ is a Rademacher sum in the entries of $\sigma$, and for $K\neq\emptyset$ its coefficients satisfy $\sum_{(a,i)}c_{e,w,z}(a,i)^2=\|w\|^2\|z\|^2/|K|$, so finite sign-tail bounds apply. Selections are injective maps rather than subsets, so labels keep their identities. Combined with nets of the unit spheres and a union bound, the development obtains, whenever $k\ge1$ and $2n^p\,9^{k+p}e^{-25k/2}<1$, a sign matrix $\sigma$ on $\{1,\dots,k\}\times\{1,\dots,n\}$ all of whose selections of $p$ columns satisfy $\|\Phi^\sigma_e\|\le10$.
--
--   **Formalization Note** The definitions are `SignMatrix.extend`, `SignMatrix.vector`, `SignMatrix.synthesis` and `SignMatrix.testCoefficients`, with selections given as embeddings `J ↪ I`. If $K$ is empty then $\sqrt{|K|}=0$, and Lean's convention $x/0=0$ makes these vectors and coefficients zero. This real `SignMatrix.synthesis` is distinct from the complex `FiniteSynthesis.synthesis`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/SignMatrix.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/SignMatrix.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DixmierAllDiscrete mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Regular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis__DixmierAllDiscrete

namespace OAI

/-! Normalized sign matrices and their finite-dimensional bilinear
tests. The coordinate selections are injective and retain label identities. -/
noncomputable section
namespace Dixmier
namespace SignMatrix
open Finset
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
local instance instDecidableEq_oAI_2 : DecidableEq K := Classical.decEq K

def extend (e : J ↪ I) (z : J → ℝ) : I → ℝ := Function.extend e z (fun _ => 0)

omit [Fintype I] [Fintype J] in
@[simp] theorem extend_apply (e : J ↪ I) (z : J → ℝ) (j : J) : extend e z (e j) = z j :=
  e.injective.extend_apply z _ j

def vector (σ : K × I → Bool) (i : I) : EuclideanSpace ℝ K :=
  WithLp.toLp 2 (fun a => FiniteSigns.sign (σ (a,i)) / Real.sqrt (Fintype.card K))

omit [Fintype I] in
@[simp] theorem vector_apply (σ : K × I → Bool) (i : I) (a : K) :
    vector σ i a = FiniteSigns.sign (σ (a,i)) / Real.sqrt (Fintype.card K) := rfl

def synthesis (σ : K × I → Bool) (e : J ↪ I) : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ K :=
  ∑ j : J, InnerProductSpace.rankOne ℝ (vector σ (e j)) (EuclideanSpace.basisFun J ℝ j)

omit [Fintype I] in
@[simp] theorem synthesis_apply (σ : K × I → Bool) (e : J ↪ I) (z : EuclideanSpace ℝ J) :
    synthesis σ e z = ∑ j, z j • vector σ (e j) := by
  simp only [synthesis, _root_.sum_apply, InnerProductSpace.rankOne_apply, EuclideanSpace.basisFun_inner]

def testCoefficients (e : J ↪ I) (w : EuclideanSpace ℝ K) (z : EuclideanSpace ℝ J) : K × I → ℝ :=
  fun ai => w ai.1 * extend e z ai.2 / Real.sqrt (Fintype.card K)

end SignMatrix
end Dixmier

end

end OAI



-- Prove2me | Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
-- name    : OAI_Analysis_ProductSpaces_WeakNullity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:58:05.018296+00:00
-- url     : https://prove2.me/theorems/113d3a20-17f8-4ed2-bc58-e115ecc1b7fe
-- title:
--   The contraction $L^2\to L^1$ and child increments of path products in $L^2$
-- statement:
--   1. **The inclusion of $L^2$ into $L^1$.** For a probability space $(\alpha,\nu)$, $J_\nu:L^2(\nu)\to L^1(\nu)$ is the canonical inclusion, sending the class of a square-integrable function to its class in $L^1(\nu)$. It is a continuous linear map with
--
--      $$\|J_\nu f\|_{L^1(\nu)}\le\|f\|_{L^2(\nu)}\qquad(f\in L^2(\nu)),$$
--
--      so its operator norm is at most $1$.
--
--   2. **Child increments in $L^2$.** Let $\mu$ be a Borel probability measure on $\mathbb R$ with $\int w^2\,d\mu<\infty$, and let $\mathbb P_\mu$ be the product of independent copies of $\mu$ indexed by the nonroot vertices of the tree of finite sequences of positive integers. For a vertex $v$ and $n\in\mathbb N$, the child increment is
--
--      $$\Delta_{v,n}=\pi_{\operatorname{child}(v,n)}-\pi_v\in L^2(\mathbb P_\mu),$$
--
--      where $\pi_v$ is the path product of $v$ and $\operatorname{child}(v,n)$ is $v$ extended by the integer $n+1$. Almost everywhere, $\Delta_{v,n}(\omega)=\pi_v(\omega)\,\big(\omega_{\operatorname{child}(v,n)}-1\big)$.
--
--   These objects let one study the $L^1$ differences $P_{\operatorname{child}(v,n)}-P_v$ in the product span through Hilbert-space geometry: when $\mu$ has mean one, the increments along the children of a fixed vertex are mutually orthogonal in $L^2$ with constant norm, and $J$ maps each of them to the corresponding $L^1$ difference.
--
--   **Formalization Note** The inclusion is `l2ToL1 ν`, built with `LinearMap.mkContinuous` and bound $1$; the increment is `childIncrementL2 μ h₂ v n`, the difference of the `MemLp.toLp` classes of the two path products, where `h₂` is the finite-second-moment hypothesis.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/WeakNullity.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/WeakNullity.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndependentProducts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uH uα

namespace IndependentProducts
section HilbertTools

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable {α : Type uα} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]

/-- The canonical continuous inclusion L2 -> L1 on a probability space. -/
def l2ToL1 : Lp ℝ 2 ν →L[ℝ] Lp ℝ 1 ν :=
  ({ toFun := fun f => ⟨f.val, (Lp.antitone (by norm_num : (1 : ℝ≥0∞) ≤ 2)) f.property⟩
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 1 ν).mkContinuous 1 (by
    intro f
    simp only [one_mul, Lp.norm_def]
    apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.aestronglyMeasurable f))

end HilbertTools

section ChildL2
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]
variable (h₂ : MemLp (fun w : ℝ => w) 2 μ)

/-- The child jump in the Hilbert space L2. -/
def childIncrementL2 (v : Vertex) (n : ℕ) : Lp ℝ 2 (productMeasure μ) :=
  (pathProduct_memLp μ h₂ (child v n)).toLp (pathProduct (child v n)) -
    (pathProduct_memLp μ h₂ v).toLp (pathProduct v)

end ChildL2
end IndependentProducts

namespace IndependentProducts

end IndependentProducts

end

end OAI



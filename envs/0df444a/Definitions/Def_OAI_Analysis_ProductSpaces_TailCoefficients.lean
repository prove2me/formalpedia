-- Prove2me | Definitions.Def_OAI_Analysis_ProductSpaces_TailCoefficients
-- name    : OAI_Analysis_ProductSpaces_TailCoefficients
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:11:34.961185+00:00
-- url     : https://prove2.me/theorems/477d11f6-bb71-4e58-b023-0de68ac02149
-- title:
--   Residual path products and first-exit tail coefficients on the tree of positive-integer sequences
-- statement:
--   Let $\mathcal V$ be the rooted tree of finite sequences $v=(v_1,\dots,v_m)$ of positive integers, with root the empty sequence $\varnothing$, let $\mathcal E=\mathcal V\setminus\{\varnothing\}$ be the set of nonroot vertices, and let a sample be a point $\omega=(\omega_d)_{d\in\mathcal E}\in\mathbb{R}^{\mathcal E}$, one real coordinate per nonroot vertex. For a vertex $v$ write $v|_j=(v_1,\dots,v_j)$ for its prefix of length $j$, $E(v)=\{v|_1,\dots,v|_{m}\}\subseteq\mathcal E$ for the set of its nonempty prefixes, and $\Pi_v(\omega)=\prod_{d\in E(v)}\omega_d$ for its path product (equal to $1$ at the root).
--
--   The file introduces two objects.
--
--   1. **Residual product.** For a vertex $v$, a nonroot vertex $e$ and a sample $\omega$,
--
--      $$R_{v,e}(\omega)=\prod_{d\in E(v)\setminus E(e)}\omega_d .$$
--
--      When $e$ is a prefix of $v$, this is the product of the coordinates on the part of the path to $v$ strictly below $e$, so that $\Pi_v=\Pi_e\,R_{v,e}$; in particular $R_{e,e}=1$.
--
--   2. **Tail coefficient.** Let $T$ be a finite head, i.e. a finite set of vertices that contains the root and is closed under taking prefixes, and let $\partial T$ be its boundary: the nonroot vertices $e\notin T$ whose parent $e^-$ (delete the last entry) lies in $T$. Fix finite index sets $\iota$ and $\kappa$, boundary vertices $e:\iota\to\partial T$, vertices $v:\kappa\to\mathcal V$, an assignment $j:\kappa\to\iota$ and real coefficients $a:\kappa\to\mathbb{R}$. For two samples $\omega^{\mathrm{old}},\omega^{\mathrm{desc}}\in\mathbb{R}^{\mathcal E}$ and an index $i\in\iota$, the tail coefficient is
--
--      $$C_i\bigl(\omega^{\mathrm{old}},\omega^{\mathrm{desc}}\bigr)=\sum_{k\in\kappa:\ j(k)=i}a_k\,\Pi_{e_i^-}\bigl(\omega^{\mathrm{old}}\bigr)\,R_{v_k,e_i}\bigl(\omega^{\mathrm{desc}}\bigr).$$
--
--   These are the bookkeeping devices for a first-exit decomposition of a finite linear combination $\sum_k a_k\Pi_{v_k}$ of path products. Each $v_k$ is grouped according to the boundary vertex $e_{j(k)}$ through which its path leaves the head; the part of the path above the exit is read from the old coordinates, and the part below the $i$-th exit from a fresh descendant sample $\omega^{\mathrm{desc},i}$. When $e$ is injective and every $v_k$ lies below $e_{j(k)}$, the combination evaluated on a sample stitched together in this way becomes $\sum_i C_i\bigl(\omega^{\mathrm{old}},\omega^{\mathrm{desc},i}\bigr)\,\omega_{e_i}$, in which each exit coordinate $\omega_{e_i}$ is multiplied by a coefficient that does not involve it. This conditional independence below the exit forest is what the resampling estimates for the averaged midpoint modulus of the span of path products rely on.
--
--   **Formalization Note** In Lean the residual product is `residualProduct v e ω`, where $E(\cdot)$ is the finset `pathEdges`, and the tail coefficient is `FiniteHead.tailCoefficient T e v j a old i desc`; the parent $e_i^-$ is obtained with `List.dropLast`. The definition itself does not require $e$ to be injective or $v_k$ to lie below $e_{j(k)}$; such conditions are imposed by the lemmas that use it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/TailCoefficients.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/TailCoefficients.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndependentProducts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_FiniteHeads
import Definitions.Def_OAI_Analysis_ProductSpaces_Resampling
import Definitions.Def_OAI_Analysis_ProductSpaces_ClosedTails

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι uκ

namespace IndependentProducts
section FiniteRepresentatives
variable (μ : Measure ℝ) [hμprob : IsProbabilityMeasure μ]
  (h₂ : MemLp (fun w : ℝ => w) 2 μ)

namespace FiniteHead
variable (T : FiniteHead)

end FiniteHead
end FiniteRepresentatives

/-- Descendant-only factor after the first exit. -/
def residualProduct (v : Vertex) (e : Edge) (ω : Sample) : ℝ :=
  ∏ d ∈ pathEdges v \ pathEdges e.val, ω d

namespace FiniteHead
section FiniteTailData
variable {ι : Type uι} {κ : Type uκ} [hιfinite : Fintype ι] [Fintype κ] [DecidableEq ι]
variable (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)

/-- Coefficients conditionally independent below the exit forest. -/
noncomputable def tailCoefficient (old : Sample) (i : ι) (desc : Sample) : ℝ :=
  ∑ k, if j k = i then a k * pathProduct (e i).val.val.dropLast old *
    residualProduct (v k) (e i).val desc else 0

end FiniteTailData
end FiniteHead
end IndependentProducts

end

end OAI



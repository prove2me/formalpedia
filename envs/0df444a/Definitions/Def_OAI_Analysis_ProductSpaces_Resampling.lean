-- Prove2me | Definitions.Def_OAI_Analysis_ProductSpaces_Resampling
-- name    : OAI_Analysis_ProductSpaces_Resampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:08:35.977905+00:00
-- url     : https://prove2.me/theorems/904d9edb-cbfd-4bc6-8a50-9ec6f19b4a19
-- title:
--   Stitching independent samples along the exit boundary of a finite head
-- statement:
--   Let $E$ be the set of nonroot vertices of the tree of finite sequences of positive integers, a sample being a point $\omega\in\mathbb R^{E}$. Fix a finite index set $\iota$, a finite head $T$ (a finite prefix-closed set of vertices containing the root) and a family $(e_i)_{i\in\iota}$ of first-exit vertices of $T$ (vertices outside $T$ whose parent lies in $T$).
--
--   1. **Expanded samples.** Given a triple $z=((\xi,\eta),\omega)$ consisting of a family $\xi=(\xi_i)_{i\in\iota}$ of samples, a sample $\eta$ and a sample $\omega$, $\operatorname{expand}(z)$ is the family of samples indexed by $\{\mathrm{old},\mathrm{exit}\}\sqcup\iota$ with
--
--      $$\operatorname{expand}(z)_{\mathrm{old}}=\omega,\qquad\operatorname{expand}(z)_{\mathrm{exit}}=\eta,\qquad\operatorname{expand}(z)_{i}=\xi_i .$$
--
--   2. **Sample selector.** For an edge $d\in E$: if some $e_i$ is a prefix of $d$ (choose such an $i$), then $\operatorname{sel}(d)=\mathrm{exit}$ when $d=e_i$ and $\operatorname{sel}(d)=i$ otherwise; if no $e_i$ is a prefix of $d$, then $\operatorname{sel}(d)=\mathrm{old}$.
--
--   3. **Stitched sample.** $\operatorname{stitch}(z)\in\mathbb R^{E}$ is defined coordinatewise by
--
--      $$\operatorname{stitch}(z)(d)=\operatorname{expand}(z)_{\operatorname{sel}(d)}(d),$$
--
--      so coordinates in the head and away from the chosen exits are read from $\omega$, coordinates on the exit edges from $\eta$, and coordinates strictly below the exit $e_i$ from the sample $\xi_i$.
--
--   If the samples $\xi_i$ ($i\in\iota$), $\eta$ and $\omega$ are independent, each with the product law $\mu^{\otimes E}$ for a probability measure $\mu$ on $\mathbb R$, then the stitched sample again has law $\mu^{\otimes E}$. This resampling device is used to rewrite tail vectors of the $L^1$ product span, conditionally on the head coordinates, as sums over the exits with independent coefficient blocks and independent exit multipliers.
--
--   **Formalization Note** The index set $\{\mathrm{old},\mathrm{exit}\}\sqcup\iota$ is `Option (Option ι)`, with `none` for the old coordinates, `some none` for the exit coordinates and `some (some i)` for the $i$-th descendant block; the definitions are `expandSamples`, `FiniteHead.sampleSelector` and `FiniteHead.stitched`. The choice of $i$ in the selector uses `Classical.choose`; it is unique when the exits $e_i$ are distinct.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/Resampling.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/Resampling.lean by skeleton subtraction
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

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι

namespace IndependentProducts

section Resampling
variable {ι : Type uι} [Fintype ι]

/-- Independent complete samples: descendants, exits, and old coordinates. -/
def expandSamples (z : ((ι → Sample) × Sample) × Sample) : Option (Option ι) → Sample
  | none => z.2
  | some none => z.1.2
  | some (some i) => z.1.1 i

namespace FiniteHead
variable (T : FiniteHead) (e : ι → T.Boundary) (he : Function.Injective e)

noncomputable def sampleSelector (d : Edge) : Option (Option ι) := by
  classical
  exact if h : ∃ i, (e i).val.val <+: d.val then
    if d = (e (Classical.choose h)).val then some none else some (some (Classical.choose h))
  else none

noncomputable def stitched (z : ((ι → Sample) × Sample) × Sample) : Sample :=
  fun d => expandSamples z (T.sampleSelector e d) d

end FiniteHead

namespace FiniteHead
variable (T : FiniteHead) (e : ι → T.Boundary) (he : Function.Injective e)

end FiniteHead
end Resampling
end IndependentProducts

end

end OAI



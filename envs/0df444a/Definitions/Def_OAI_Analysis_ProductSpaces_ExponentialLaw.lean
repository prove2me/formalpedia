-- Prove2me | Definitions.Def_OAI_Analysis_ProductSpaces_ExponentialLaw
-- name    : OAI_Analysis_ProductSpaces_ExponentialLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:45:38.369257+00:00
-- url     : https://prove2.me/theorems/713f6522-1026-48ec-96d4-05df040f437f
-- title:
--   The standard exponential law is a probability measure
-- statement:
--   Let $\mathrm{Exp}(1)$ denote the standard exponential distribution on $\mathbb{R}$, the Borel measure with density $e^{-w}$ for $w\ge0$ and density $0$ for $w<0$:
--
--   $$\mathrm{Exp}(1)(A)=\int_{A\cap[0,\infty)}e^{-w}\,dw\qquad(A\subseteq\mathbb{R}\ \text{Borel}).$$
--
--   This file records that $\mathrm{Exp}(1)$ is a probability measure, $\mathrm{Exp}(1)(\mathbb{R})=\int_0^\infty e^{-w}\,dw=1$.
--
--   The exponential law is one of the concrete multiplier laws of the independent-products construction: putting independent $\mathrm{Exp}(1)$ coordinates on the nonroot vertices of the tree of finite sequences of positive integers gives the product measure whose closed $L^1$ span of path products is studied in the exponential case. Registering the probability property once makes infinite product measures, finite product measures and expectations with respect to $\mathrm{Exp}(1)$ available without further proof obligations.
--
--   **Formalization Note** The law itself, `exponentialLaw`, is defined in the base file as Mathlib's `expMeasure 1` (rate $1$). This file only adds the type-class instance `exponentialLaw_probability`, stating `IsProbabilityMeasure exponentialLaw`, obtained from Mathlib's `isProbabilityMeasure_expMeasure`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/ExponentialLaw.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/ExponentialLaw.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_ProductSpaces_TailCoefficients

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uE

namespace IndependentProducts

instance exponentialLaw_probability : IsProbabilityMeasure exponentialLaw :=
  isProbabilityMeasure_expMeasure (by norm_num)

end IndependentProducts

end

end OAI



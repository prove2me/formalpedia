-- Prove2me | Definitions.Def_ConservativeAD_AutoDiff_ConservativeField
-- name    : ConservativeAD_AutoDiff_ConservativeField
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:37:59.648661+00:00
-- url     : https://prove2.me/theorems/fa3f9fc5-2435-4cc0-8272-042d39f3f1ad
-- title:
--   Locally bounded set-valued maps (the hypothesis of Lemma 2)
-- statement:
--   Let $X$ be a topological space and $Y$ a space with a notion of bounded set (here $X=Y=\mathbb R^n$). A set-valued map $D:X\rightrightarrows Y$, assigning to each $x\in X$ a subset $D(x)\subseteq Y$, is **locally bounded** if every point $x$ has a neighbourhood $U$ such that
--
--   $$
--   \bigcup_{y\in U}D(y)\ \text{is bounded}.
--   $$
--
--   Local boundedness is the first hypothesis of Lemma 2 (chain rule and conservativity), and Remark 3(d) uses it to show that potentials of conservative fields are locally Lipschitz. In this mission it is a hypothesis of Lemma 2 and of Theorem 8 (on the elementary fields $D_k$).
--
--   **Formalization Note** Conservative fields and their potentials (Definitions 1–2) are the shared definitions `ConservativeAD.GradAE.IsConservative` and `ConservativeAD.GradAE.IsPotential`, imported by this module; this item adds only local boundedness. The bornology on `EuclideanSpace ℝ (Fin n)` is the metric one, so "bounded" has its usual meaning.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), p. 8, Lemma 2 (locally bounded); pp. 7–8, Remark 3(d)

import Mathlib
import Definitions.Def_ConservativeAD_GradAE_ConservativeField
open MeasureTheory

namespace ConservativeAD.AutoDiff

/-- A set-valued map `D : X ⇒ Y` into a normed space is locally bounded if every point has a
neighbourhood `U` on which `⋃_{y ∈ U} D y` is bounded (the hypothesis of Lemma 2). -/
def IsLocallyBounded {X Y : Type*} [TopologicalSpace X] [Bornology Y] (D : X → Set Y) : Prop :=
  ∀ x, ∃ U ∈ nhds x, Bornology.IsBounded (⋃ y ∈ U, D y)

end ConservativeAD.AutoDiff



-- Prove2me | Definitions.Def_GeometryOfGraphs_Clique_isoDim
-- name    : GeometryOfGraphs_Clique_isoDim
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:59:19.932807+00:00
-- url     : https://prove2.me/theorems/b142d18f-d86e-47d0-8ad4-6b59dfac0545
-- title:
--   Isometric dimension of a finite metric space
-- statement:
--   The **isometric dimension** of a finite metric space $(X,\delta)$ is the least nonnegative integer $d$ for which $X$ embeds isometrically into some real normed space of dimension $d$:
--
--   $$
--   \dim(X,\delta)=\min\{d\in\mathbb N:X\text{ embeds isometrically in dimension }d\}.
--   $$
--
--   This invariant asks for the smallest dimension across all real norms, rather than fixing one particular $\ell_p$ norm.
--
--   **Formalization Note** The set infimum on natural numbers represents the minimum. For a finite pseudometric space this set is nonempty by Lemma 5.1; on an arbitrary distance function with no realization, the totalized infimum returns zero. Every theorem here uses a realizable distance.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), pp. 218–219, Definition 2.1 and isometric dimension

import Definitions.Def_GeometryOfGraphs_Clique_EmbedsIsometrically

namespace GeometryOfGraphs.Clique

/-- The least dimension of a real normed space admitting an isometric embedding. -/
noncomputable def isoDim {X : Type*} (δ : X → X → ℝ) : ℕ :=
  sInf {d : ℕ | EmbedsIsometrically d δ}

end GeometryOfGraphs.Clique



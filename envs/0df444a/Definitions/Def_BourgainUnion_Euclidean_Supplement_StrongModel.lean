-- Prove2me | Definitions.Def_BourgainUnion_Euclidean_Supplement_StrongModel
-- name    : BourgainUnion_Euclidean_Supplement_StrongModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:31:52.337201+00:00
-- url     : https://prove2.me/theorems/ecddff6b-ec8b-47f3-857c-4f7f24941cf0
-- title:
--   2-strongly Euclidean subsets
-- statement:
--   Let $(X,d)$ be a metric space and $V\subseteq X$. Following §1.1, $V$ is **$h$-strongly Euclidean** in $X$ if $V\cup S$ embeds isometrically into $\ell_2$ for every $h$-element set $S\subseteq X$. For $h=2$ this definition records
--   $$V \text{ Euclidean and } V\cup\{x,y\}\text{ Euclidean for all } x,y\in X,$$
--   where "Euclidean" is the published predicate: the set, with the induced distance, admits an isometric map into $\ell_2$.
--
--   Allowing $x=y$ gives the same notion, because $V\cup\{x\}\subseteq V\cup\{x,y\}$; it also gives the right answer when $X$ has fewer than two points, where every subset is Euclidean. The 1-strongly Euclidean notion is the published `OneStrong`. Theorem 1.1 and Claim 2.5 are stated with this predicate.
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 2, §1.1 (Euclidean classes)

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_EmbeddingModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean.Supplement

open BourgainUnion.Euclidean

/-- §1.1, p. 2: `V` is 2-strongly Euclidean in `X` when `V ∪ S` embeds isometrically into `ℓ₂`
for every two-element `S ⊆ X`. Quantifying over all pairs `x, y` (allowing `x = y`) is the same
condition, since `V ∪ {x} ⊆ V ∪ {x, y}`, and it also covers spaces with fewer than two points. -/
def TwoStrong {X : Type*} [PseudoMetricSpace X] (V : Set X) : Prop :=
  IsEuclidean V ∧ ∀ x y : X, IsEuclidean (V ∪ {x, y})

end BourgainUnion.Euclidean.Supplement



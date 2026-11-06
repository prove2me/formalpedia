-- Prove2me | Definitions.Def_TreeMultiflow_IsStarBinInstance
-- name    : TreeMultiflow_IsStarBinInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:11.3929+00:00
-- url     : https://prove2.me/theorems/4102c89d-0935-4fab-870d-58197c44b392
-- title:
--   Bins of an attached star with precoloured crossing paths (hypotheses of Lemma 5.1)
-- statement:
--   Consider the bins at the leaves of an attached star. A **local path** has its two ends in two bins $\beta_1(l)$ and $\beta_2(l)$; a **crossing path** $c$ has one end in the star, in the bin $\beta(c)$, and has already been given a colour $\kappa(c)$ from a palette of ten colours. The hypotheses common to both cases of Lemma 5.1 are:
--
--   1. the two ends of every local path lie in different bins;
--   2. every bin contains at most six paths (local path ends together with crossing paths);
--   3. crossing paths in the same bin have distinct colours.
--
--   **Formalization Note** Only the bin incidences of the star are kept. A local path joins two distinct leaves adjacent to the star's centre and every bin lies at one leaf, so its two ends are in different bins; conversely every such instance arises from a star with one bin per leaf.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Lemma 5.1, p.8 (bins at the leaves of an attached star)

import Mathlib
import Definitions.Def_TreeMultiflow_pathEnd

namespace TreeMultiflow

open Classical in
/-- **Bins at the leaves of an attached star, with precoloured crossing paths (Lemma 5.1).**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Lemma 5.1,
p.8: "Consider the bins at the leaves of an attached star. Every bin contains at most six paths.
Suppose the crossing paths have already been assigned colors from a set of ten colors, with
distinct colors within each bin."

The bins are the elements of a type `B`. Each local path `l : L` has its two ends in the bins
`l₁ l` and `l₂ l`; each crossing path `c : C` has one end in the star, in the bin `cb c`, and the
colour `κ c ∈ Fin 10`. `IsStarBinInstance l₁ l₂ cb κ` says

1. the two ends of every local path lie in different bins;
2. every bin contains at most six paths (local path ends plus crossing paths);
3. distinct crossing paths in the same bin have distinct colours.

**Formalization Note.** A local path joins two distinct leaves adjacent to the star centre
(p.7), and every bin lives at one leaf, so its two ends are in two different bins; conversely
every instance of this form arises from a star with one bin per leaf. The tree itself plays no
role in Lemma 5.1, so only the bin incidences are kept. The ends of `l` are `(l, false)` and
`(l, true)` (see `pathEnd`). -/
def IsStarBinInstance {B L C : Type*} [Fintype L] [Fintype C] (l₁ l₂ : L → B) (cb : C → B)
    (κ : C → Fin 10) : Prop :=
  (∀ l, l₁ l ≠ l₂ l) ∧
  (∀ β : B, (Finset.univ.filter fun ξ : L × Bool => pathEnd l₁ l₂ ξ = β).card +
      (Finset.univ.filter fun c => cb c = β).card ≤ 6) ∧
  (∀ c c' : C, c ≠ c' → cb c = cb c' → κ c ≠ κ c')

end TreeMultiflow



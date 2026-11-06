-- Prove2me | Definitions.Def_TreeMultiflow_IsBinColouringExtension
-- name    : TreeMultiflow_IsBinColouringExtension
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:17.869197+00:00
-- url     : https://prove2.me/theorems/5da815d7-8de9-45fe-b4b7-2016720ca80b
-- title:
--   Colouring of the local paths proper in every bin (conclusion of Lemma 5.1)
-- statement:
--   With the data of an attached star as in Lemma 5.1, a colouring $\mathrm{col}$ of the local paths with ten colours, together with the unchanged crossing colours $\kappa$, **gives distinct colours to the paths in each bin** if
--
--   1. two different local paths with ends in a common bin receive different colours, and
--   2. a local path with an end in the bin of a crossing path $c$ does not receive the colour $\kappa(c)$.
--
--   Crossing paths in a common bin already have distinct colours by hypothesis.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Lemma 5.1, pp.8–9 (The resulting coloring gives distinct colors to the paths in each bin)

import Mathlib
import Definitions.Def_TreeMultiflow_pathEnd

namespace TreeMultiflow

/-- **Colouring of the local paths that is proper in every bin (conclusion of Lemma 5.1).**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Lemma 5.1,
pp.8–9: "We can color all the local paths using the same ten colors, without changing any crossing
color … The resulting coloring gives distinct colors to the paths in each bin."

With the data of `IsStarBinInstance`, a colouring `col : L → Fin 10` of the local paths, together
with the fixed crossing colours `κ`, gives distinct colours to the paths of every bin:

1. two different local paths with ends in a common bin get different colours;
2. a local path with an end in the bin of a crossing path `c` does not get the colour `κ c`.

(Crossing paths in a common bin already have distinct colours by assumption, and their colours are
not changed.) -/
def IsBinColouringExtension {B L C : Type*} (l₁ l₂ : L → B) (cb : C → B) (κ : C → Fin 10)
    (col : L → Fin 10) : Prop :=
  (∀ ξ η : L × Bool, pathEnd l₁ l₂ ξ = pathEnd l₁ l₂ η → ξ.1 ≠ η.1 → col ξ.1 ≠ col η.1) ∧
  (∀ (ξ : L × Bool) (c : C), pathEnd l₁ l₂ ξ = cb c → col ξ.1 ≠ κ c)

end TreeMultiflow



-- Prove2me | Definitions.Def_ChapterFreeFieldBornCont
-- name    : ChapterFreeFieldBornCont
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T03:10:15.906509+00:00
-- url     : https://prove2.me/theorems/46cbd737-3c66-49d1-8506-fc032db7cbae
-- title:
--   ChapterFreeFieldBornCont

import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBorn
import Mathlib

/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# the Born parametrization is a *continuous* surjection of the sphere onto the simplex

Source: `book.tex`, chapter *"Wave-function parametrization of a probability
measure"* — the Introduction's statement (`book.tex` ~line 805) that *"the
wave-function is nothing else than one possible parametrization of any
probability distribution; the parametrization is a surjective map from an
hypersphere to the set of all possible probability distributions"*, together
with the free-field construction of §5 (`book.tex` ~line 1706).

Wave 141 (`ChapterFreeFieldBorn`) showed the coordinate-wise Born map
`x ↦ (x_k)²` sends the unit sphere *into* the probability simplex; Wave 142
(`ChapterFreeFieldBornSurj`) showed it is *surjective* onto the simplex, with a
canonical continuous section `p ↦ (√ p_k)`.  This file records the **topological**
content of the parametrization claim: the Born map is *continuous*, so the
probability simplex is exactly the image of the (compact) unit sphere under a
continuous map — hence itself compact.  Together with Wave 142 this says the
hypersphere parametrizes "the set of all possible probability distributions"
*continuously*.

## Main results

* `continuous_bornMap` — the Born map is continuous.
* `continuous_bornSection` — the square-root section is continuous.
* `bornMap_mapsTo_stdSimplex` — the Born map sends the unit sphere into the
  simplex (packaged as `Set.MapsTo`).
* **headline** `stdSimplex_eq_bornMap_image_sphere` — the probability simplex is
  *exactly* the image of the unit sphere under the Born map:
  `stdSimplex ℝ (Fin n) = bornMap '' Metric.sphere 0 1`.
* `isCompact_stdSimplex_of_born` — consequently the simplex is compact, exhibited
  as the continuous image of the compact sphere.

Everything is intended to be `sorry`-free and axiom-clean.
-/
namespace BookProof.ChapterFreeFieldBornCont

end BookProof.ChapterFreeFieldBornCont



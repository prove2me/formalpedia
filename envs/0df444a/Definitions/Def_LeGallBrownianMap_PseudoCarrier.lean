-- Prove2me | Definitions.Def_LeGallBrownianMap_PseudoCarrier
-- name    : LeGallBrownianMap_PseudoCarrier
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:58.241993+00:00
-- url     : https://prove2.me/theorems/12e06761-042f-489d-9c00-0a7ed408b966
-- title:
--   Auxiliary copy of a set carrying a given pseudometric
-- statement:
--   Given a set $X$ and a function $d : X \times X \to \mathbb R$, this is a second copy of $X$ on which $d$ will be installed as a pseudometric, so that it does not interfere with any structure $X$ already has (for instance the Euclidean metric of $[0,1]$).
--
--   It is a purely technical device used by the construction of the quotient metric space $X/\{d=0\}$ as a point of $\mathbb K$.
--
--   **Formalization Note** A type synonym `PseudoCarrier X d := X` with no instances.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §1, pp.2–4 (metric spaces built from pseudometrics)

import Mathlib

namespace LeGallBrownianMap

/-- A type synonym of `X` that carries no instances, on which a function `d : X → X → ℝ` is
installed as a pseudometric by `LeGallBrownianMap.pseudoQuotientGH`. It is used to turn a
pseudometric space such as `([0,1], D∗)` (Le Gall, arXiv:1105.4842v2, §1, eq. (1), p.4) or a
finite vertex set with a scaled graph distance (§1, p.2) into a point of the space K of
isometry classes of compact metric spaces.

**Formalization Note.** The synonym exists only so that the pseudometric given by `d` does not
clash with instances `X` may already carry (for instance the Euclidean metric of
`unitInterval`). -/
def PseudoCarrier (X : Type) (_d : X → X → ℝ) : Type := X

end LeGallBrownianMap



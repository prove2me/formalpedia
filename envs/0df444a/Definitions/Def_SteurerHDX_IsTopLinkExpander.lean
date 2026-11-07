-- Prove2me | Definitions.Def_SteurerHDX_IsTopLinkExpander
-- name    : SteurerHDX_IsTopLinkExpander
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:34:23.633029+00:00
-- url     : https://prove2.me/theorems/af8651ca-0186-4da3-be45-2905307a4b55
-- title:
--   $\alpha$-top-link spectral expander
-- statement:
--   A $d$-dimensional complex $\mathcal X$ is an **$\alpha$-top-link expander** if
--   $$\lambda_2(\tau)\le\alpha\qquad\text{for every face }\tau\text{ of codimension }2,$$
--   i.e. for every $\tau\in\mathcal X$ with $|\tau|=d-2$.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Definition 2.2, p.3

import Mathlib
import Definitions.Def_SteurerHDX_lambdaTau

namespace SteurerHDX

/-- **Top-link spectral expander.** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Definition 2.2, p.3: "We say X is an α-top-link
expander if λ₂(τ) ≤ α for any τ of co-dimension 2."

**Formalization Note.** co-dimension 2 for a d-dimensional complex means `τ.card + 2 = d`
(dimension = cardinality). -/
def IsTopLinkExpander {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (d : ℕ) (a : ℝ) :
    Prop :=
  ∀ τ ∈ X, τ.card + 2 = d → lambdaTau X τ ≤ a

end SteurerHDX



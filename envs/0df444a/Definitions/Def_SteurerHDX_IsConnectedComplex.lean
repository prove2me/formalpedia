-- Prove2me | Definitions.Def_SteurerHDX_IsConnectedComplex
-- name    : SteurerHDX_IsConnectedComplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:31:36.57372+00:00
-- url     : https://prove2.me/theorems/a84d6661-5797-48c6-a97f-bc11bb69023d
-- title:
--   Connected complex
-- statement:
--   A $d$-dimensional complex $\mathcal X$ is **connected** if for every face $\tau$ of **codimension** $\operatorname{codim}(\tau)=d-|\tau|\ge 2$ (including $\tau=\emptyset$), the 1-skeleton of the link $\mathcal X_\tau$ is a connected graph.
--
--   **Formalization Note** $\operatorname{codim}(\tau)\ge 2$ is written $|\tau|+2\le d$; Lean's notion of a connected graph also requires a nonempty vertex set, which these links of a pure complex have.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Section 2.2, p.3

import Mathlib
import Definitions.Def_SteurerHDX_link
import Definitions.Def_SteurerHDX_skeleton1

namespace SteurerHDX

/-- **Connected complex.** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Section 2.2, p.3: "the codimension of a face τ ∈ X is
defined as codim(τ) = d − dim(τ)" and "We say X is a connected complex if for every τ of
codimension at least 2, the 1-skeleton of X_τ is a connected graph."

**Formalization Note.** codim(τ) ≥ 2 is written `τ.card + 2 ≤ d` (dimension = cardinality, no
natural-number subtraction); τ = ∅ is included. `SimpleGraph.Connected` also requires a
nonempty vertex set, which every such link of a pure d-dimensional complex has. -/
def IsConnectedComplex {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (d : ℕ) : Prop :=
  ∀ τ ∈ X, τ.card + 2 ≤ d → (skeleton1 (link X τ)).Connected

end SteurerHDX



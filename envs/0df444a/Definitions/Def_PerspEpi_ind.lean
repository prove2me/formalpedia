-- Prove2me | Definitions.Def_PerspEpi_ind
-- name    : PerspEpi_ind
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:30.480602+00:00
-- url     : https://prove2.me/theorems/c1eb36c4-f26b-4d75-8f17-b285e5915f13
-- title:
--   Indicator function $\delta_C$
-- statement:
--   For a set $C$, the **indicator function** $\delta_C : X \to \overline{\mathbb R}$ is
--
--   $$
--   \delta_C(x) = \begin{cases} 0 & x \in C,\\ +\infty & x \notin C.\end{cases}
--   $$
--
--   Its subdifferential is the normal cone $N_C = \partial \delta_C$, and the paper's projections arise as proximal maps of indicators ($\delta_{\operatorname{epi} f}$, $\delta_{\operatorname{lev}_\alpha f}$).
--
--   **Formalization Note** Valued in `EReal`.
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, §1.2 Notation, p.4

import Mathlib

namespace PerspEpi

/-- **Indicator function.** Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, §1.2 Notation, p.4:
"δ_C(x) := 0 if x ∈ C and δ_C(x) = +∞ otherwise".

**Formalization Note.** Valued in `EReal`. -/
noncomputable def ind {X : Type*} (C : Set X) : X → EReal :=
  fun x => by classical exact if x ∈ C then 0 else ⊤

end PerspEpi



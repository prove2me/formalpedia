-- Prove2me | Definitions.Def_GnpColoring_IsFeasible
-- name    : GnpColoring_IsFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:52.88618+00:00
-- url     : https://prove2.me/theorems/ddc06984-8135-444a-96a8-fdf82a1791bb
-- title:
--   Feasible boundary condition
-- statement:
--   A colouring $\tau$ of $V\setminus U$ is **feasible** if it extends to a proper $q$-colouring of $G$.
--
--   **Formalization Note** The boundary condition is given as a full colouring $x$, of which only the values off $U$ matter.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 2.2, p.13

import Mathlib
import Definitions.Def_mm_coupling

open scoped Classical
open Finset

namespace GnpColoring

/-- **Feasible boundary condition**: the colouring `x` restricted to `V ∖ U` extends to a proper
`q`-colouring of `G`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 2.2, p.13: "A boundary condition τ on V ∖ U is feasible if it extends to a proper
coloring of G."

**Formalization Note** The boundary condition `τ` is given as a full colouring `x`; only its
values off `U` matter. -/
def IsFeasible {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (U : Finset (Fin n)) (x : Fin n → Fin q) :
    Prop :=
  ∃ σ : Fin n → Fin q, MarkovMixing.IsProperColoring G σ ∧ ∀ w, w ∉ U → σ w = x w

end GnpColoring



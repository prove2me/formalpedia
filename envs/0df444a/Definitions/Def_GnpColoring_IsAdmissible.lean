-- Prove2me | Definitions.Def_GnpColoring_IsAdmissible
-- name    : GnpColoring_IsAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:51.704014+00:00
-- url     : https://prove2.me/theorems/bb65d9b3-17fd-4c4f-8876-2445c069cd06
-- title:
--   Admissible boundary condition
-- statement:
--   A colouring $\tau$ of $V\setminus T$ is **admissible** for $T$ if it is feasible and every $w\in T$ with a neighbour outside $T$ has $\deg_G(w)\le\bar\Delta$: no hub of $T$ touches the exterior.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 5.1.1, p.44

import Mathlib
import Definitions.Def_GnpColoring_IsFeasible
import Definitions.Def_GnpColoring_deltaBar

open scoped Classical
open Finset

namespace GnpColoring

/-- **Admissible boundary condition** on `T`: feasible, and every `w ∈ T` with a neighbour in
`V ∖ T` has `deg_G(w) ≤ Δ̄`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 5.1.1, p.44: "A feasible boundary condition is called admissible if every w ∈ T
with a neighbor in V ∖ T satisfies deg_G(w) ≤ Δ̄." -/
def IsAdmissible {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (d η : ℝ) (T : Finset (Fin n))
    (x : Fin n → Fin q) : Prop :=
  IsFeasible G q T x ∧ ∀ w ∈ T, (∃ u, u ∉ T ∧ G.Adj w u) → (G.degree w : ℝ) ≤ deltaBar d η

end GnpColoring



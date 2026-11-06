-- Prove2me | Definitions.Def_GnpColoring_heatBathMatrix
-- name    : GnpColoring_heatBathMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:37.662228+00:00
-- url     : https://prove2.me/theorems/eb5bf365-6388-49af-a918-03a1aa4fb8c7
-- title:
--   The heat-bath update $P_U$ as a transition matrix
-- statement:
--   For a vertex set $U$, $P_U(x,y)=\mu(y)/\mu(\{z:z=x\text{ off }U\})$ if $y$ agrees with $x$ off $U$, and $0$ otherwise: resample the colours of $U$ from $\mu$ given the rest.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 2.3, p.14

import Mathlib

open scoped Classical
open Finset

namespace GnpColoring

/-- **The heat-bath update of a vertex set `U`** as a transition matrix: from `x`, resample the
colours on `U` from `µ` conditioned on the colours off `U`,
`P_U(x, y) = µ(y) / µ({z : z = x off U})` if `y = x` off `U`, and `0` otherwise.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 2.3, p.14: "For colorings, let P_U f = E_µ[f | σ_{V∖U}] be the heat-bath update of U."

**Formalization Note** Rows at configurations outside the support of `µ` are junk; the matrix is
only used restricted to proper colourings. -/
noncomputable def heatBathMatrix {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (U : Finset (Fin n)) :
    Matrix (Fin n → Fin q) (Fin n → Fin q) ℝ :=
  fun x y => if ∀ w, w ∉ U → y w = x w then
      μ y / ∑ z ∈ univ.filter (fun z : Fin n → Fin q => ∀ w, w ∉ U → z w = x w), μ z
    else 0

end GnpColoring



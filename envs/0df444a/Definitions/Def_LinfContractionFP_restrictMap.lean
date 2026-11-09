-- Prove2me | Definitions.Def_LinfContractionFP_restrictMap
-- name    : LinfContractionFP_restrictMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:15:20.227597+00:00
-- url     : https://prove2.me/theorems/1eee0e4f-7168-429a-9b96-51d350285bb3
-- title:
--   The restricted maps $y\mapsto f_S(y,q_{-S})$
-- statement:
--   For a set $S$ of coordinates and a point $q$, the **restricted map** sends $y\in\mathbb R^S$ to the $S$-coordinates of $f(y,q_{-S})$, where $(y,q_{-S})$ is the point with coordinates $y_i$ for $i\in S$ and $q_i$ otherwise, and $f$ is the clipped extension.
--
--   ThinLabel solves these maps recursively for the narrow set $S=N$ and the wide set $S=W$, with $q$ the centre of the box.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Section 3, p.5; Section 5, p.8; Algorithm 2, lines 6–7, p.9

import Mathlib
import Definitions.Def_LinfContractionFP_clipExt

open scoped Classical

namespace LinfContractionFP

/-- The restricted map `y ↦ f_S(y, q_{−S})` of Section 5 on the coordinates `S ⊆ ι`: the
coordinates outside `S` are fixed to those of `q`, the clipped extension of `f` is evaluated,
and its output is restricted to `S`.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Section 3, p.5 ("For any
N ⊆ [d], let x_N denote the subvector containing only the coordinates in N, and let x_{−N}
denote its restriction to the complementary coordinates. Similarly, f_N(x) denotes the
restriction of f(x) to the coordinates in N") and Section 5, p.8 ("The algorithm recursively
invokes Solve at precision γη/2 on the maps y ↦ f_N(y, q_{−N}) and y ↦ f_W(q_{−W}, y)").

**Formalization Note.** The restricted map lives on `↥S → ℝ` (`S` a `Finset ι`); the same
definition serves the narrow (`S = N`) and the wide (`S = W`) map, the order of the arguments
in `f_W(q_{−W}, y)` being notation. The map uses `clipExt f`, the paper's standing extension
(Section 3), because `q` may lie outside the cube. -/
noncomputable def restrictMap {ι : Type} (f : (ι → ℝ) → (ι → ℝ)) (S : Finset ι) (q : ι → ℝ) :
    (↥S → ℝ) → (↥S → ℝ) := fun y j =>
  clipExt f (fun i => if h : i ∈ S then y ⟨i, h⟩ else q i) j

end LinfContractionFP



-- Prove2me | Definitions.Def_LinfContractionFP_IsNearFixed
-- name    : LinfContractionFP_IsNearFixed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:55.322341+00:00
-- url     : https://prove2.me/theorems/006d6655-a6c1-4ed0-afbe-7d2781ed4fc4
-- title:
--   $\varepsilon$-near fixed point
-- statement:
--   A point $x$ is an **$\varepsilon$-near fixed point** of $f$ if $x\in[0,1]^\iota$ and
--   $$\|x-x^*\|_\infty\le\varepsilon$$
--   for the fixed point $x^*$ of $f$ in $[0,1]^\iota$. This is the output guarantee of Theorem 1.
--
--   **Formalization Note** The fixed point is not named: the inequality is required for every fixed point of $f$ in the cube. For a $(1-\gamma)$-contraction with $0<\gamma\le1$ there is exactly one, so this is the paper's notion and it is not vacuous.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Section 1, p.1

import Mathlib
import Definitions.Def_LinfContractionFP_unitCube

namespace LinfContractionFP

/-- `x` is an `ε`-near fixed point of `f`: `x ∈ [0,1]^ι` and `‖x − x*‖∞ ≤ ε` for the fixed point
`x*` of `f` in the cube.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Section 1, p.1: "a point
x ∈ [0, 1]^d is [...] an ε-near fixed point if ‖x − x*‖∞ ≤ ε", where x* is the unique fixed
point given by Banach's theorem.

**Formalization Note.** The fixed point is not named: the condition is required for every fixed
point `y` of `f` in the cube. For a `(1 − γ)`-contraction with `0 < γ ≤ 1` there is exactly one
(proved in the mission's sanity file), so this is the page's notion and is not vacuous. This is
the *near* notion, not the weaker approximate one (`IsApproxFixed`). -/
def IsNearFixed {ι : Type} [Fintype ι] (f : (ι → ℝ) → (ι → ℝ)) (ε : ℝ) (x : ι → ℝ) : Prop :=
  x ∈ unitCube ι ∧ ∀ y ∈ unitCube ι, f y = y → ‖x - y‖ ≤ ε

end LinfContractionFP



-- Prove2me | Definitions.Def_LinfContractionFP_IsApproxFixed
-- name    : LinfContractionFP_IsApproxFixed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:59.629536+00:00
-- url     : https://prove2.me/theorems/b0c5d40a-714c-4aa4-abbc-a253aa486bca
-- title:
--   $\eta$-approximate fixed point
-- statement:
--   A point $x$ is an **$\eta$-approximate fixed point** of $f$ if $x\in[0,1]^\iota$ and
--   $$\|f(x)-x\|_\infty\le\eta.$$
--   This is the weaker of the two notions of Section 1; ThinLabel returns such points.
--
--   **Formalization Note** Membership in the cube is part of the notion because the paper defines it for "a point $x\in[0,1]^d$".
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Section 1, p.1

import Mathlib
import Definitions.Def_LinfContractionFP_unitCube

namespace LinfContractionFP

/-- `x` is an `η`-approximate fixed point of `f`: `x ∈ [0,1]^ι` and `‖f(x) − x‖∞ ≤ η`.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Section 1, p.1: "For
ε > 0, a point x ∈ [0, 1]^d is an ε-approximate fixed point if ‖f(x) − x‖∞ ≤ ε".

**Formalization Note.** Membership in the cube is part of the notion, because the page defines
it for "a point x ∈ [0, 1]^d". The norm is written `‖x − f x‖`, equal to `‖f x − x‖`. -/
def IsApproxFixed {ι : Type} [Fintype ι] (f : (ι → ℝ) → (ι → ℝ)) (η : ℝ) (x : ι → ℝ) : Prop :=
  x ∈ unitCube ι ∧ ‖x - f x‖ ≤ η

end LinfContractionFP



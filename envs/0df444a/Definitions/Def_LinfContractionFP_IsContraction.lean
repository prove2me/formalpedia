-- Prove2me | Definitions.Def_LinfContractionFP_IsContraction
-- name    : LinfContractionFP_IsContraction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:50.78995+00:00
-- url     : https://prove2.me/theorems/b1ae3d0f-e7c3-4334-b473-c29bc6e0ef06
-- title:
--   $f$ is a $(1-\gamma)$-contraction of $[0,1]^d$ in $\ell_\infty$
-- statement:
--   A map $f:\mathbb R^\iota\to\mathbb R^\iota$ is a **$(1-\gamma)$-contraction of the unit cube** if it maps $[0,1]^\iota$ into itself and
--   $$\|f(x)-f(y)\|_\infty\le(1-\gamma)\,\|x-y\|_\infty\qquad\text{for all }x,y\in[0,1]^\iota.$$
--   The number $\gamma$ is the **contraction gap**; the paper takes $\gamma\in(0,1]$.
--
--   This is the class of maps whose near fixed points the algorithm computes.
--
--   **Formalization Note** In Lean $f$ is total on $\mathbb R^\iota$ and its values off the cube are unconstrained; the paper's $f$ has domain $[0,1]^d$. The range $\gamma\in(0,1]$ is not built in: every theorem assumes $0<\gamma\le1$. No monotonicity is assumed.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Section 1, p.1

import Mathlib
import Definitions.Def_LinfContractionFP_unitCube

namespace LinfContractionFP

/-- `f` is a `(1 − γ)`-contraction of the unit cube in the ℓ∞ norm: it maps `[0,1]^ι` into
itself and `‖f x − f y‖∞ ≤ (1 − γ) ‖x − y‖∞` for all `x, y ∈ [0,1]^ι`.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Section 1, p.1: "Let
f : [0, 1]^d → [0, 1]^d be an ℓ∞-contraction. Thus, for some γ ∈ (0, 1],
‖f(x) − f(y)‖∞ ≤ (1 − γ) ‖x − y‖∞ for all x, y ∈ [0, 1]^d."

**Formalization Note.** Lean's `f` is total on `ι → ℝ`; its values off the cube are
unconstrained (the paper's `f` has domain `[0,1]^d`; the algorithm only ever uses the clipped
extension `clipExt f`). The range `γ ∈ (0, 1]` is not bundled: every theorem assumes
`0 < γ` and `γ ≤ 1`. No monotonicity or continuity off the cube is assumed. `‖·‖` on `ι → ℝ` is
Mathlib's sup norm, which is `ℓ∞`. -/
def IsContraction {ι : Type} [Fintype ι] (γ : ℝ) (f : (ι → ℝ) → (ι → ℝ)) : Prop :=
  Set.MapsTo f (unitCube ι) (unitCube ι) ∧
    ∀ x ∈ unitCube ι, ∀ y ∈ unitCube ι, ‖f x - f y‖ ≤ (1 - γ) * ‖x - y‖

end LinfContractionFP



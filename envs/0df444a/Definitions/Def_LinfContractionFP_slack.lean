-- Prove2me | Definitions.Def_LinfContractionFP_slack
-- name    : LinfContractionFP_slack
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:57.536622+00:00
-- url     : https://prove2.me/theorems/1bb49d0a-db59-4231-95ca-ffcc2629ec11
-- title:
--   Face slacks $\sigma_{i,-}=x^*_i-L_i$, $\sigma_{i,+}=U_i-x^*_i$
-- statement:
--   For a box $[L,U]=\prod_i[L_i,U_i]$, possibly degenerate ($L_i>U_i$ allowed), and a point $x^*$, the **slacks** of the $2d$ faces are
--   $$\sigma_{i,-}=x^*_i-L_i,\qquad \sigma_{i,+}=U_i-x^*_i .$$
--   They measure how far the fixed point lies from each face, and a labeling must detect the faces of extremal slack.
--
--   **Formalization Note** A face is a pair $(i,s)$ with $s=\mathtt{false}$ for $-$ and $s=\mathtt{true}$ for $+$.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Definition 1, p.6

import Mathlib

namespace LinfContractionFP

/-- The slacks of the `2d` faces of a box `[L, U]` with respect to a point `xs` (the fixed point
`x*`): `σ_{i,−} = xs_i − L_i` and `σ_{i,+} = U_i − xs_i`.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Definition 1, p.6: "we
denote the distances from the extrema L_i and U_i to the i-th coordinate of the fixed point,
x*_i, as σ_{i,−} := x*_i − L_i, and σ_{i,+} := U_i − x*_i."

**Formalization Note.** A face is a pair `(i, s) : ι × Bool`, with `s = false` the face `−`
(at `L_i`) and `s = true` the face `+` (at `U_i`). The box may be degenerate (`L_i > U_i` is
allowed), as in Definition 1. The point `xs` is a parameter; theorems assume it is the fixed
point. -/
def slack {ι : Type} (L U xs : ι → ℝ) : ι × Bool → ℝ
  | (i, false) => xs i - L i
  | (i, true) => U i - xs i

end LinfContractionFP



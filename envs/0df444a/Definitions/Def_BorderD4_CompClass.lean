-- Prove2me | Definitions.Def_BorderD4_CompClass
-- name    : BorderD4_CompClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:17.038046+00:00
-- url     : https://prove2.me/theorems/c6e0e401-980d-43b8-8bd5-473d0c41aa29
-- title:
--   Sums of compositions $C_d(m,r;L)$
-- statement:
--   $C_d(m,r;L)$ is the set of polynomials
--   $$G=\sum_{i=1}^m f_i(g_{i,1},\dots,g_{i,r}),$$
--   with arbitrary outer polynomials $f_i\in L[y_1,\dots,y_r]$ and inner polynomials $g_{i,j}\in L[u]$ of degree at most $d$. These are the sums of $m$ compositions of arity $r$.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 6.4, p.50

import Mathlib
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- The class `C_d(m, r; L)` of sums of `m` compositions of arity `r`:
`G = ∑_{i=1}^m f_i(g_{i,1}, …, g_{i,r})` with arbitrary outer polynomials `f_i ∈ L[y_1, …, y_r]` and inner
polynomials `g_{i,j} ∈ L[u]` of degree at most `d`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 6.4, p.50. -/
def CompClass (L τ : Type*) [Field L] (d m r : ℕ) : Set (MvPolynomial τ L) :=
  {G | ∃ (f : Fin m → MvPolynomial (Fin r) L) (g : Fin m → Fin r → MvPolynomial τ L),
    (∀ i j, (g i j).totalDegree ≤ d) ∧ G = ∑ i, aeval (g i) (f i)}

end BorderD4



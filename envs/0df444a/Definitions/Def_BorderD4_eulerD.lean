-- Prove2me | Definitions.Def_BorderD4_eulerD
-- name    : BorderD4_eulerD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:30.55819+00:00
-- url     : https://prove2.me/theorems/c19c7a98-2135-4df8-bd2f-8f1df1996a9a
-- title:
--   The Euler derivation $D$ in the free coordinates
-- statement:
--   For $p\in F[[\varepsilon]][x]$, $Dp=\sum_{i\in T}x_i\,\partial_{x_i}p$. It treats $\varepsilon$ and the dependent coordinates as constants and does not increase degree in $x$.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.3.4, p.68

import Mathlib
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- The Euler derivation in the free coordinates, `Dp = ∑_{i∈T} x_i ∂_{x_i} p`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.3.4 "Differentiation", p.68. -/
noncomputable def eulerD {F σ : Type*} [Field F] (T : Finset σ) (p : MvPolynomial σ F⟦X⟧) :
    MvPolynomial σ F⟦X⟧ :=
  ∑ i ∈ T, X i * pderiv i p

end BorderD4



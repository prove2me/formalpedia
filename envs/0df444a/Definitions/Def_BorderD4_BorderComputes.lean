-- Prove2me | Definitions.Def_BorderD4_BorderComputes
-- name    : BorderD4_BorderComputes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:59:05.253531+00:00
-- url     : https://prove2.me/theorems/d85de6b4-6222-4ecb-b4ce-2c71e0441bf3
-- title:
--   Border computation by a circuit over $F((\varepsilon))$
-- statement:
--   A circuit $\Phi$ over the Laurent series field $F((\varepsilon))$ border computes $f\in F[x]$ if
--   $$\Phi \text{ computes } f+\varepsilon S\quad\text{for some } S\in F[[\varepsilon]][x].$$
--   The size of the border computation is the size of $\Phi$.
--
--   **Formalization Note** The polynomial $S$ has coefficients in $F[[\varepsilon]]$. This integrality is the content of the definition: over $F((\varepsilon))$ every polynomial would be approximated by the zero circuit.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 2.12, p.33

import Mathlib
import Definitions.Def_BorderD4_SPSP
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- The variable `ε` as an element of `F((ε))`. -/
noncomputable def epsK (F : Type*) [Field F] : LaurentSeries F :=
  algebraMap F⟦X⟧ (LaurentSeries F) PowerSeries.X

/-- `C` border computes `f`: the circuit `C` over `F((ε))` computes `f + εS` for some `S ∈ F[[ε]][x]`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 2.12, p.33.

**Formalization Note** `S` has coefficients in `F[[ε]]`, which is the content of the definition: with `S`
over `F((ε))` every polynomial would be border computed by the zero circuit. The size of the border
computation is `C.size`. -/
def BorderComputes {F σ : Type*} [Field F] {k δ : ℕ} (C : SPSP (LaurentSeries F) σ k δ)
    (f : MvPolynomial σ F) : Prop :=
  ∃ S : MvPolynomial σ F⟦X⟧,
    C.eval = map (algebraMap F (LaurentSeries F)) f
      + MvPolynomial.C (epsK F) * map (algebraMap F⟦X⟧ (LaurentSeries F)) S

end BorderD4



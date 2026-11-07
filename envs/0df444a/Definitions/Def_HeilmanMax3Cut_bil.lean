-- Prove2me | Definitions.Def_HeilmanMax3Cut_bil
-- name    : HeilmanMax3Cut_bil
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:12.537528+00:00
-- url     : https://prove2.me/theorems/96d1d478-0f2f-44b8-bed8-f45d182f341e
-- title:
--   The form $\langle x,Ky\rangle$ on $L^2(\nu)$
-- statement:
--   For a kernel $K(t,s)$ on $(0,\infty)^2$ and functions $x,y$ on $(0,\infty)$,
--
--   $$\langle x,Ky\rangle=\int_0^\infty\!\!\int_0^\infty x(t)\,K(t,s)\,y(s)\,d\nu(s)\,d\nu(t),$$
--
--   the $L^2(\nu)$ pairing of $x$ with the integral operator with kernel $K$ applied to $y$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), (105), p.31

import Mathlib
import Definitions.Def_HeilmanMax3Cut_nuExp
open MeasureTheory

namespace HeilmanMax3Cut

/-- **The form `⟨x, K y⟩` on `L²(ν)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), (105), p.31: for the integral operator with kernel
`K`, `⟨x, K y⟩ = ∫₀^∞ ∫₀^∞ x(t) K(t, s) y(s) dν(s) dν(t)`, where `⟨·, ·⟩` is the `L²` inner product
on `(0, ∞)` with respect to `ν`.

**Formalization Note.** An iterated Bochner integral against `ν`. -/
noncomputable def bil (K : ℝ → ℝ → ℝ) (x y : ℝ → ℝ) : ℝ :=
  ∫ t, ∫ s, x t * K t s * y s ∂nuExp ∂nuExp

end HeilmanMax3Cut



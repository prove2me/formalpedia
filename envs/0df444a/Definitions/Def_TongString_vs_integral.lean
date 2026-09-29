-- Prove2me | Definitions.Def_TongString_vs_integral
-- name    : TongString_vs_integral
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T20:16:56.87207+00:00
-- url     : https://prove2.me/theorems/fea50ea5-1d8d-4b16-921b-c9aea9460ca9
-- title:
--   The Virasoro–Shapiro integral $C(a,b)=\int d^2z\,|z|^{2a-2}|1-z|^{2b-2}$
-- statement:
--   For complex numbers $a,b$ the **Virasoro–Shapiro integral** is
--
--   $$
--   C(a,b)=\int_{\mathbb C} d^2z\,|z|^{2a-2}\,|1-z|^{2b-2},\qquad d^2z=2\,dx\,dy\quad (z=x+iy),
--   $$
--
--   that is, twice the Lebesgue integral over the plane of the function $z\mapsto |z|^{2a-2}|1-z|^{2b-2}$, where for a real $r>0$ and complex $w$ one sets $r^{w}=e^{w\log r}$.
--
--   This is the integral to which the closed-string four-tachyon amplitude reduces after fixing the $SL(2,\mathbb C)$ gauge (eq. (6.10)); its closed form (6.11) is the Virasoro–Shapiro amplitude.
--
--   **Formalization Note** The integral is Mathlib's Bochner integral with respect to the Lebesgue (Haar) measure `volume` on `ℂ`; it equals $0$ when the integrand is not integrable, so theorems about it carry the convergence conditions $\operatorname{Re}a>0$, $\operatorname{Re}b>0$, $\operatorname{Re}(a+b)<1$. Powers are principal-branch complex powers of the non-negative reals $|z|$, $|1-z|$; at the two points $z=0,1$ they take junk values, which does not affect the integral.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 6.2.2 p. 137 eq. (6.11) and Appendix 6.5 p. 157 (definition of C(a,b), measure convention d^2z = 2 dx dy from p. 158)

import Mathlib

namespace TongString

open MeasureTheory

/-- Tong's integral `C(a, b) = ∫ d²z |z|^(2a-2) |1-z|^(2b-2)` with the convention
`d²z = 2 dx dy`, i.e. twice the Lebesgue integral over `ℂ ≃ ℝ²`. -/
noncomputable def virasoroShapiroIntegral (a b : ℂ) : ℂ :=
  2 * ∫ z : ℂ, ((‖z‖ : ℂ) ^ (2 * a - 2)) * ((‖1 - z‖ : ℂ) ^ (2 * b - 2))

end TongString



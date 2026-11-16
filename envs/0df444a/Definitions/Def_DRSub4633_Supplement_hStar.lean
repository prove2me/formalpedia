-- Prove2me | Definitions.Def_DRSub4633_Supplement_hStar
-- name    : DRSub4633_Supplement_hStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:33:53.856259+00:00
-- url     : https://prove2.me/theorems/be661e3d-f4b4-4546-9291-c26fc0bda250
-- title:
--   The sharp recovery map $h_\star$, Eq. (137)
-- statement:
--   The coordinatewise map $h_\star:\mathbb R^n\to\mathbb R^n$ given by
--   $$(h_\star(x))_i=\begin{cases}1-e^{-x_i}, & x_i\le s_\star,\\[2pt] \dfrac{x_i}{b_\star+x_i}, & x_i>s_\star.\end{cases}$$
--   At the threshold $x_i=s_\star$ the exponential branch gives the value, so the map has an upward jump from the right there. It uses $b_\star=\sqrt3/2$, not the parameter $b$ of the base mission's recovery map.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Appendix B.1, Eq. (137), p.53

import Mathlib
import Definitions.Def_DRSub4633_Supplement_bStar
import Definitions.Def_DRSub4633_Supplement_sStar

namespace DRSub4633.Supplement

/-- **The recovery map `h⋆`, Eq. (137).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Appendix B.1, Eq. (137), p.53:
"`(h⋆(x))ᵢ = 1 − e^{−xᵢ}` if `xᵢ ≤ s⋆`, `xᵢ/(b⋆ + xᵢ)` if `xᵢ > s⋆`. At the threshold, the
exponential branch specifies the value."

**Formalization Note.** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`; the map is applied coordinatewise.
It uses `b⋆ = √3/2`, not the base mission's `b` (`DRSub4633.hRec`). -/
noncomputable def hStar {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => if x i ≤ sStar then 1 - Real.exp (-x i) else x i / (bStar + x i))

end DRSub4633.Supplement



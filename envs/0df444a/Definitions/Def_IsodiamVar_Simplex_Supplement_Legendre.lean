-- Prove2me | Definitions.Def_IsodiamVar_Simplex_Supplement_Legendre
-- name    : IsodiamVar_Simplex_Supplement_Legendre
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:48:39.204689+00:00
-- url     : https://prove2.me/theorems/8ed5c383-3abf-450d-bdfc-a08b3fc2d4c9
-- title:
--   Equation (1.6) — Euclidean conjugate and biconjugate of φ_K
-- statement:
--   For the function $\phi_K$ of (1.5), use the Euclidean pairing to identify points with continuous linear functionals, and set
--
--   $$\phi_K^*(p)=\sup_{x\in\mathbb R^n}\{\langle p,x\rangle-\phi_K(x)\},\qquad
--   \phi_K^{**}(x)=\sup_{p\in\mathbb R^n}\{\langle x,p\rangle-\phi_K^*(p)\}.$$
--
--   These are genuine suprema in $[-\infty,+\infty]$, computed by the referenced generic conjugate. They retain the infinite values needed for empty sets and points outside the closed convex hull. In particular, $\phi_\varnothing^*=-\infty$ and $\phi_\varnothing^{**}=+\infty$.
-- source:
--   Lim & McCann, Geometrical bounds for the variance and recentered moments, arXiv:2001.11851v1, p. 2, (1.5)–(1.6)

import Definitions.Def_IsodiamVar_Simplex_Supplement_Phi
import Definitions.Def_WassersteinDRO_ConvexLossP1_conjugate

open MeasureTheory

namespace IsodiamVar.Simplex.Supplement

/-- Equation (1.6), p. 2, under the Euclidean identification with the dual.
The generic published conjugate uses genuine EReal suprema. -/
noncomputable def phiStar {n : ℕ} (K : Set (E n)) (p : E n) : EReal :=
  WassersteinDRO.ConvexLossP1.conjugate (phi K) (innerSL ℝ p)

/-- Double Legendre transform, with the canonical Euclidean double-dual pairing. -/
noncomputable def phiBiconjugate {n : ℕ} (K : Set (E n)) (x : E n) : EReal :=
  WassersteinDRO.ConvexLossP1.conjugate (phiStar K) (innerSL ℝ x)

end IsodiamVar.Simplex.Supplement



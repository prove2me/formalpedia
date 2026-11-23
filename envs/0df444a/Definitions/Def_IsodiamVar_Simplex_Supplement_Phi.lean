-- Prove2me | Definitions.Def_IsodiamVar_Simplex_Supplement_Phi
-- name    : IsodiamVar_Simplex_Supplement_Phi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:46:59.058399+00:00
-- url     : https://prove2.me/theorems/e6c7932a-0f0a-4e77-8719-6f6524b15586
-- title:
--   Equation (1.5) — negative squared norm restricted to K
-- statement:
--   For $K\subseteq\mathbb R^n$, define the extended-real function
--
--   $$\phi_K(x)=\begin{cases}-|x|^2,&x\in K,\\+\infty,&x\notin K.\end{cases}$$
--
--   The convex envelope of this function controls the greatest second moment at a prescribed mean. The empty set gives the function constantly equal to $+\infty$.
-- source:
--   Lim & McCann, Geometrical bounds for the variance and recentered moments, arXiv:2001.11851v1, p. 2, (1.5)

import Definitions.Def_IsodiamVar_Simplex_Defs

open MeasureTheory Classical

namespace IsodiamVar.Simplex.Supplement

/-- Equation (1.5), p. 2: negative squared norm on K and +∞ elsewhere. -/
noncomputable def phi {n : ℕ} (K : Set (E n)) (x : E n) : EReal :=
  if x ∈ K then ((-(‖x‖ ^ 2) : ℝ) : EReal) else ⊤

end IsodiamVar.Simplex.Supplement



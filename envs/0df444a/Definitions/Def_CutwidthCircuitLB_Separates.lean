-- Prove2me | Definitions.Def_CutwidthCircuitLB_Separates
-- name    : CutwidthCircuitLB_Separates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:29.435688+00:00
-- url     : https://prove2.me/theorems/065cf206-bead-436b-8580-1f143c9101e5
-- title:
--   A threshold separates two reals
-- statement:
--   A threshold $t \in \mathbb R$ **separates** two reals $a, b$ if it lies strictly between them: $\min(a, b) < t < \max(a, b)$.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Appendix A, p.21

import Mathlib

namespace CutwidthCircuitLB

/-- A threshold `t` **separates** two reals `a, b` if it lies strictly between them (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3),
Appendix A, p.21): `min(a, b) < t < max(a, b)`. -/
def Separates (t a b : ℝ) : Prop :=
  min a b < t ∧ t < max a b

end CutwidthCircuitLB



-- Prove2me | Definitions.Def_SampleRemoval_Supplement_saddleLift
-- name    : SampleRemoval_Supplement_saddleLift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:18:43.629837+00:00
-- url     : https://prove2.me/theorems/9f239b05-c1b8-4dcf-822a-14f23a721aa1
-- title:
--   Saddle lift $\widehat p_i=(x_iy_i,x_i,y_i)$
-- statement:
--   The **saddle lift** maps a planar point $p_i=(x_i,y_i)$ to
--
--   $$\widehat p_i=(x_iy_i,x_i,y_i)\in\mathbb R^3.$$
--
--   Plane cuts of these lifted points are the conic range family studied in Section 5.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Sections 2 and 5, pp.3,8 (PDF pp.5,10)

import Mathlib

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- The saddle lift `p̂ᵢ=(xᵢyᵢ,xᵢ,yᵢ)∈ℝ³` (Xu, Gao, Hu, STOC 2027 submission,
§5.1, p.8 (PDF p.10)). Coordinates `0,1,2` are respectively `xy,x,y`. -/
def saddleLift {n : ℕ} (p : Fin n → ℝ × ℝ) (i : Fin n) : Fin 3 → ℝ :=
  fun j => if j.1 = 0 then (p i).1 * (p i).2 else if j.1 = 1 then (p i).1 else (p i).2

end SampleRemoval.Supplement



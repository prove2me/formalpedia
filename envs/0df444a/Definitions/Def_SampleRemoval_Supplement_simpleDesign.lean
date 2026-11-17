-- Prove2me | Definitions.Def_SampleRemoval_Supplement_simpleDesign
-- name    : SampleRemoval_Supplement_simpleDesign
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:18:11.697497+00:00
-- url     : https://prove2.me/theorems/83610786-a9d9-4bf0-b780-025f01bfbaf1
-- title:
--   Intercept-plus-one-regressor design of planar data
-- statement:
--   A planar observation $p_i=(x_i,y_i)$ determines the simple-regression design row $(1,x_i)$, with $y_i$ as response. This is the intercept-plus-one-regressor representation used throughout Section 5.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Sections 2 and 5, pp.3,8 (PDF pp.5,10)

import Mathlib

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- The intercept-plus-one-regressor design associated with planar data `pᵢ=(xᵢ,yᵢ)`:
the design row is `(1,xᵢ)` (Xu, Gao, Hu, STOC 2027 submission, §2 and §5, pp.3,8
(PDF pp.5,10)). -/
def simpleDesign {n : ℕ} (p : Fin n → ℝ × ℝ) : Fin n → Fin 2 → ℝ :=
  fun i j => if j.1 = 0 then 1 else (p i).1

end SampleRemoval.Supplement



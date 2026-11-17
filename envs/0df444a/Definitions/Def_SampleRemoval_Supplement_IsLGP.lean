-- Prove2me | Definitions.Def_SampleRemoval_Supplement_IsLGP
-- name    : SampleRemoval_Supplement_IsLGP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:19:14.254077+00:00
-- url     : https://prove2.me/theorems/d44484a3-36ef-47dc-8632-4b5e94ed0464
-- title:
--   Lifted general position (LGP)
-- statement:
--   Planar data are in **lifted general position** when no four saddle lifts $\widehat p_i=(x_iy_i,x_i,y_i)$ are coplanar. Equivalently, every four distinct lifted points are affinely independent.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Section 5.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_SampleRemoval_Supplement_saddleLift

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- Lifted general position (LGP): every four saddle lifts are affinely independent, equivalently
no four are coplanar (Xu, Gao, Hu, STOC 2027 submission, §5.1, p.9 (PDF p.11)). -/
def IsLGP {n : ℕ} (p : Fin n → ℝ × ℝ) : Prop :=
  ∀ s : Finset (Fin n), s.card = 4 → AffineIndependent ℝ (fun i : s => saddleLift p i)

end SampleRemoval.Supplement



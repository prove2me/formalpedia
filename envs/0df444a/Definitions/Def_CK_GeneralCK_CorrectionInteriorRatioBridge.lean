-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionInteriorRatioBridge
-- name    : CK_GeneralCK_CorrectionInteriorRatioBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:07:24.179627+00:00
-- url     : https://prove2.me/theorems/711333d5-627d-4196-98a0-75895343e655
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionInteriorRatioBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionInteriorRatioBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionInteriorRatioBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionInteriorRatioBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionInteriorRatioBridge.lean)

import Definitions.Def_CK_GeneralCK_CorrectionHessianNatural

namespace GeneralCK.Correction.Natural

/-- A closed interval certificate may have `rho ≤ 1`; the actual entropy
Hessian bridge only evaluates interior points, for which `rho < 1` is supplied
separately by the ordered-triangle domain. -/
theorem ratio_point_interior {u rho : ℝ} (hhalf : 0 < 1/2-u)
    (hr : 0 < rho) (hr1 : rho < 1) :
    u < u+rho*(1/2-u) ∧ u+rho*(1/2-u) < 1/2 := by
  constructor
  · nlinarith [mul_pos hr hhalf]
  · nlinarith [mul_pos (sub_pos.mpr hr1) hhalf]

/-- Ratio-coordinate form of `kernel_eq_actual`. No strict upper bound is
required of a surrounding certificate box; only the evaluated point has to
satisfy `rho < 1`. -/
theorem kernel_eq_actual_ratio {u rho : ℝ} (hu : 0 < u) (hhalf : 0 < 1/2-u)
    (hr : 0 < rho) (hr1 : rho < 1) :
    m11 u (u+rho*(1/2-u)) = Mleft (H u) (H (u+rho*(1/2-u))) ∧
    kdet u (u+rho*(1/2-u)) = Kfactored (H u) (H (u+rho*(1/2-u))) := by
  obtain ⟨huw, hw⟩ := ratio_point_interior hhalf hr hr1
  exact kernel_eq_actual hu huw hw

#print axioms ratio_point_interior
#print axioms kernel_eq_actual_ratio

end GeneralCK.Correction.Natural



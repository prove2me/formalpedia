-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DiagonalCurvatureCoefficient
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DiagonalCurvatureCoefficient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:27.827151+00:00
-- url     : https://prove2.me/theorems/37953b8b-ec35-4ef8-8ad5-06c481e9234a
-- title:
--   Diagonal Curvature Coefficient
-- statement:
--   Definitions and structural lemmas for Diagonal Curvature Coefficient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/DiagonalCurvatureCoefficient.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoeffMatrixZeroCorrectedLineGramPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology
variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)
section CD
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}
end CD
def fY (v : Fin 1 → ℂ) : ℝ := (Gz hm D Y (v 0)).det.re
def fn (v : Fin 1 → ℂ) : ℝ := (Gnz hm D Y (v 0)).det.re
def pd (v : Fin 1 → ℂ) : ℂ := (1 - (v 0) • Ym hm Y).det
def Sa (a : Fin m) : ℝ := ∑ k : Fin r, if m ≤ (k : ℕ) then D k * ‖Y k (Fin.castLE hm a)‖ ^ 2 else 0
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf



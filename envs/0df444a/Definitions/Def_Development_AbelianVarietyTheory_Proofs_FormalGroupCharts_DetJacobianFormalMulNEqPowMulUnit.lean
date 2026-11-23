-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_DetJacobianFormalMulNEqPowMulUnit
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_DetJacobianFormalMulNEqPowMulUnit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:38.185941+00:00
-- url     : https://prove2.me/theorems/cb660ed8-5779-497b-9197-67d5cc7c99a2
-- title:
--   Det Jacobian Formal Mul NEq Pow Mul Unit
-- statement:
--   Definitions and structural lemmas for Det Jacobian Formal Mul NEq Pow Mul Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/DetJacobianFormalMulNEqPowMulUnit.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_LawRightUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
namespace GlobalTheory.MulJacobian
variable {R : Type} [CommRing R] {d : ℕ}
def invMat (G : FGLaw R d) : Matrix (Fin d) (Fin d) (PS R 1 d) :=
  Matrix.of fun j i => ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F j))
end GlobalTheory.MulJacobian



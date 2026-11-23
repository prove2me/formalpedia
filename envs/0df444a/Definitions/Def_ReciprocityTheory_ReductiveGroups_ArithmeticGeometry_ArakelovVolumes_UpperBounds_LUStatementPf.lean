-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:45:36.859061+00:00
-- url     : https://prove2.me/theorems/243f7fd2-f9f7-4eb1-a9a3-4e9a9ac390bb
-- title:
--   LUStatement Pf
-- statement:
--   Definitions and structural lemmas for LUStatement Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LUStatementPf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
  Metric Polynomial
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}
def linePoly (x v : Frame X.Ψ r) : ℂ[X] :=
  ∏ τ, ∏ k : Fin (r + 1),
    (((Mx X x0 x τ).map C + (Polynomial.X : ℂ[X]) • ((mat x0 τ)⁻¹ * mat v τ).map C).submatrix
      (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end ReciprocityTheory.ChartRestriction.G.AR.Up



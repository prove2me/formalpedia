-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_LgCurvePcurve
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_LgCurvePcurve
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:15.24991+00:00
-- url     : https://prove2.me/theorems/16bac384-ca8c-40c8-8afb-fe37fa86e346
-- title:
--   Lg Curve Pcurve
-- statement:
--   Definitions and structural lemmas for Lg Curve Pcurve, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/LgCurvePcurve.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_EqZeroOfVecMulTmat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
def ptx (G : LogFGL v d) (p : ℕ) (γ : Fin d → Fin d → PowerSeries C)
    (ga : Fin d → PowerSeries C) (n : ℕ) : Fin d → C :=
  Matrix.vecMul (G.lc p ga n - ∑ s : Fin n, ∑ b,
    (ptx G p γ ga s b) ^ (p ^ (n - s)) • G.lc p (γ b) (n - s)) (tmat γ)⁻¹
termination_by n
decreasing_by exact s.isLt
def ptw (G : LogFGL v d) (p : ℕ) (γ : Fin d → Fin d → PowerSeries C)
    (ga : Fin d → PowerSeries C) (n : ℕ) : Fin d → C :=
  G.lc p ga n - ∑ s ∈ Finset.range n, ∑ b,
    (ptx G p γ ga s b) ^ (p ^ (n - s)) • G.lc p (γ b) (n - s)
def pcurve (G : LogFGL v d) (p : ℕ) (γ : Fin d → Fin d → PowerSeries C) (x : ℕ → Fin d → C) :
    ℕ → Fin d → PowerSeries C
  | 0 => 0
  | s + 1 => G.add (pcurve G p γ x s) (G.sumF fun b => expC (p ^ s) (rescaleCurve (x s b) (γ b)))
end
end ReciprocityTheory.ChartRestriction.G.Sh.PTb



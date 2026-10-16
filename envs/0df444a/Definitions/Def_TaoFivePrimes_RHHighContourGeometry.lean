-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighContourGeometry
-- name    : TaoFivePrimes_RHHighContourGeometry
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T11:07:53.257482+00:00
-- url     : https://prove2.me/theorems/1a512184-9684-460e-b2ca-b910ed08f853
-- title:
--   Explicit four-edge geometry of the128-unit contour
-- statement:
--   The rectangle with real bounds[-64,64] and imaginary bounds[-1/2,1/2], horizontal steps1/32, vertical stepsi/128, edge indices and orientations. Functions only, with no analytic enclosure, nonvanishing, winding, zero count or RH assertion.
-- source:
--   Platt finite-height RH window construction DOI10.1090/mcom/3198. Original attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighContourGridV2
set_option autoImplicit false
namespace RHHighContourGeometry
noncomputable def lo : ℂ := -64-Complex.I/2
noncomputable def hi : ℂ := 64+Complex.I/2
noncomputable def start (e : Nat) : ℂ :=
 if e=0 then -64-Complex.I/2 else if e=1 then 64-Complex.I/2 else if e=2 then -64+Complex.I/2 else -64-Complex.I/2
noncomputable def step (e : Nat) : ℂ := if e=0 ∨ e=2 then 1/32 else Complex.I/128
noncomputable def cells (e : Nat) : Nat := RHHighContourGridV2.cells e
noncomputable def line (e : Nat) (t : ℝ) : ℂ := start e+(t:ℂ)*step e
noncomputable def point (e j : Nat) : ℂ := line e (j:ℝ)
noncomputable def orientation (e : Nat) : Int := if e<2 then 1 else -1
end RHHighContourGeometry
noncomputable def TaoFivePrimes_RHHighContourGeometry : Nat := 8448



-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01ContourGeometry
-- name    : TaoFivePrimes_RHBatch01ContourGeometry
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T18:01:47.301988+00:00
-- url     : https://prove2.me/theorems/99bf9192-feb0-441a-9305-99df503da21c
-- title:
--   Explicit four-edge geometry of the128-unit contour
-- statement:
--   The rectangle with real bounds[-64,64] and imaginary bounds[-1/2,1/2], horizontal steps1/32, vertical stepsi/128, edge indices and orientations. Functions only, with no analytic enclosure, nonvanishing, winding, zero count or RH assertion.
-- source:
--   Platt finite-height RH window construction DOI10.1090/mcom/3198. Original attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01ContourGridV2
set_option autoImplicit false
namespace RHBatch01ContourGeometry
noncomputable def lo : ℂ := -64-Complex.I/2
noncomputable def hi : ℂ := 64+Complex.I/2
noncomputable def start (e : Nat) : ℂ :=
 if e=0 then -64-Complex.I/2 else if e=1 then 64-Complex.I/2 else if e=2 then -64+Complex.I/2 else -64-Complex.I/2
noncomputable def step (e : Nat) : ℂ := if e=0 ∨ e=2 then 1/32 else Complex.I/128
noncomputable def cells (e : Nat) : Nat := RHBatch01ContourGridV2.cells e
noncomputable def line (e : Nat) (t : ℝ) : ℂ := start e+(t:ℂ)*step e
noncomputable def point (e j : Nat) : ℂ := line e (j:ℝ)
noncomputable def orientation (e : Nat) : Int := if e<2 then 1 else -1
end RHBatch01ContourGeometry
noncomputable def TaoFivePrimes_RHBatch01ContourGeometry : Nat := 8448



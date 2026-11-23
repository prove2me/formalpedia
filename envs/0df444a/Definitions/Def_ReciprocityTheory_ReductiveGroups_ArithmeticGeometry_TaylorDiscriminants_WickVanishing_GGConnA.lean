-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConnA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConnA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:35.059317+00:00
-- url     : https://prove2.me/theorems/e7bd9db7-36c6-4ec3-b404-28f18b27deac
-- title:
--   GGConn A
-- statement:
--   Definitions and structural lemmas for GGConn A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
section Line
open Polynomial
end Line
open Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {r : ℕ} (p0 : ℕ)
def sv (a : Fin r) : ℂ := if (a : ℕ) < p0 then 1 else -1
def Gy (y : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  yᵀ * diagonal (sv p0) * y.map (starRingEnd ℂ)
def Ok (y : Matrix (Fin r) (Fin r) ℂ) : Prop := (diagonal (sv p0) * Gy p0 y).PosDef
def mask (t : ℝ) (y : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun k a => (if ((k : ℕ) < p0 ↔ (a : ℕ) < p0) then 1 else (t : ℂ)) * y k a
def Wm (s : ℂ) (y : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun k b => if ((k : ℕ) < p0 ↔ (b : ℕ) < p0) then 0 else s * conj (y k b)
variable {p0}
variable {p0 : ℕ}
end
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC



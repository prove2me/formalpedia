-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_SubtypeIteSums_CommonOfLandauEuler
-- name    : Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_SubtypeIteSums_CommonOfLandauEuler
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:26.913801+00:00
-- url     : https://prove2.me/theorems/50e1ebe6-5d02-426b-a8c2-6ed438f944b7
-- title:
--   Common Of Landau Euler
-- statement:
--   Definitions and structural lemmas for Common Of Landau Euler, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/SubtypeIteSums/CommonOfLandauEuler.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open Finset
namespace PositivityTheory.RgJS.Common0Aux
variable {W X : Type} {d : X → ℕ}
def Pw (q : W → ℕ) (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι] (u : ι → X × ℝ) (w : W) (k : ℕ) : ℂ :=
  ∑ i, ∑ a, (A (u i).1 w a * (q w : ℂ) ^ (-((u i).2 : ℂ))) ^ (k + 1)
def cc (q : W → ℕ) (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι] (u : ι → X × ℝ) (p : W × ℕ) : ℝ :=
  ‖Pw q A u p.1 p.2‖ ^ 2 / ((p.2 : ℝ) + 1)
def ll (q : W → ℕ) (p : W × ℕ) : ℝ := ((p.2 : ℝ) + 1) * Real.log (q p.1)
open Classical in

def gf {ι κ : Type} (F : ι × κ → ℂ → ℂ) (x : ι → X × ℝ) (y : κ → X × ℝ) (p : ι × κ) (s : ℂ) : ℂ :=
  if (x p.1).1 = (y p.2).1 then F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ)) / (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ) - 1)
  else F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ))
end PositivityTheory.RgJS.Common0Aux



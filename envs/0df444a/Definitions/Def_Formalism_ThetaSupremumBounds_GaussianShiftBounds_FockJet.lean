-- Prove2me | Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet
-- name    : Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:55:41.200805+00:00
-- url     : https://prove2.me/theorems/cec1447f-33b8-46ab-b13d-69ce05145f1c
-- title:
--   Fock Jet
-- statement:
--   Definitions and structural lemmas for Fock Jet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/FockJet.lean

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat
noncomputable section
namespace Formalism.DimensionVariation
def fjChi (N : ℕ) (z : ℂ) : ℂ := if ‖z‖ ≤ N then 1 else 0
def fjW (a b : ℕ) (z : ℂ) : ℂ := z ^ a * conj z ^ b * (Real.exp (-‖z‖ ^ 2) : ℂ)
def fjChiP {κ : Type} [Fintype κ] (N : ℕ) (u : κ → ℂ) : ℂ := ∏ x, fjChi N (u x)
end Formalism.DimensionVariation



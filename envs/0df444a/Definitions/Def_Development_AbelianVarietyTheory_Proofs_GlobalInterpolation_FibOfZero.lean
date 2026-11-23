-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:24.986549+00:00
-- url     : https://prove2.me/theorems/8d42512c-4f4c-4949-9562-2c338bf1436d
-- title:
--   Fib Of Zero
-- statement:
--   Definitions and structural lemmas for Fib Of Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FibOfZero.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.QuadFibre
open MeasureTheory
open scoped Pointwise
def IsSqrtOn {K : Type} [NormedField K] (U : Set K) (s : K → K) : Prop :=
  IsOpen U ∧ IsCompact U ∧ (1 : K) ∈ U ∧ (∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) ∧ (∀ a ∈ U, a⁻¹ ∈ U) ∧
    (∀ a ∈ U, ‖a‖ = 1) ∧ Continuous s ∧ ∀ a ∈ U, s a ^ 2 = a
open Classical in

def fibOf {K V : Type} [NormedField K] [MeasurableSpace K] [AddCommGroup V] [Module K V]
    [MeasurableSpace V] (μ : Measure V) (ν : Measure K) (q : V → K) (U : Set K) (s : K → K)
    (t : K) : Measure V :=
  if t = 0 then 0 else
    (ν (t • U))⁻¹ • Measure.map (fun x => s (t / q x) • x) (μ.restrict (q ⁻¹' (t • U)))
end GlobalTheory.QuadFibre



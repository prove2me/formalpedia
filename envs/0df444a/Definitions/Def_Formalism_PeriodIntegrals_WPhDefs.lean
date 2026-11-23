-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_WPhDefs
-- name    : Formalism_PeriodIntegrals_WPhDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:12.293936+00:00
-- url     : https://prove2.me/theorems/4e497843-0df5-4054-a2e4-2789b6d050fe
-- title:
--   WPh Defs
-- statement:
--   Definitions and structural lemmas for WPh Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/WPhDefs.lean

import Definitions.Def_Formalism_PeriodIntegrals_ThGDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
namespace WPhDefs
section W
variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]
noncomputable def qG (s A : ℝ) (x : T → I → J → ℂ) : ℝ := s * (HfG A x x).re
noncomputable def wPhG (s A : ℝ) (p : ℕ) (x : T → I → J → ℂ) : ℂ :=
  if p = 2 then Complex.exp ((Real.pi : ℂ) * Complex.I * (qG s A x : ℂ))
  else Classical.epsilon (fun c : ℂ => ∃ (k : ℕ) (m : ℤ), (p : ℝ) ^ k * qG s A x = (m : ℝ) ∧ c = (-1 : ℂ) ^ m)
noncomputable def WopG (s A : ℝ) (p : ℕ) (x : T → I → J → ℂ) (G : (T → I → J → ℂ) → ℂ) : (T → I → J → ℂ) → ℂ :=
  fun z => wPhG s A p x * UG A x G z
noncomputable def kapG (A : ℝ) (x y : T → I → J → ℂ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((HfG A x y).im : ℂ))
def QIntLat (s A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)) : Prop :=
  ∀ x ∈ La', (∃ m : ℤ, qG s A x = m) ∧ (x ≠ 0 → 1 ≤ qG s A x)
end W
end WPhDefs
end PI



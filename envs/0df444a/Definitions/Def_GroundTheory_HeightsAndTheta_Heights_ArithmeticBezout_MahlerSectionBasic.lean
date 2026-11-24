-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:27.081031+00:00
-- url     : https://prove2.me/theorems/2de18240-01e0-4122-9128-9619b5557d34
-- title:
--   Mahler Section Basic
-- statement:
--   Definitions and structural lemmas for Mahler Section Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/MahlerSectionBasic.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory
noncomputable section
variable {n : ℕ}
def ballH (h : HermNorm n) : Set (Fin n → ℂ) := {v | h.norm v < 1}
def nrmv (h : HermNorm n) (v : Fin n → ℂ) : Fin n → ℂ := fun j => ((h.norm v : ℝ) : ℂ)⁻¹ * v j
def cycleSection (Z : ProjCycle ℂ n) (u : Fin n → ℂ) : ProjCycle ℂ n :=
  ∑ W ∈ Z.support, Z W • divCycle W u
def GreenSymmetry.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (u u' : Fin n → ℂ),
    IsProjPrime W → (∃ g : MvPolynomial (Fin (e + 2) × Fin n) ℂ, IsChowForm W (e + 2) g) →
    linForm u ∉ W → linForm u' ∉ W → (∀ W' ∈ (divCycle W u).support, linForm u' ∉ W') →
      cycleIntegral h (divCycle W u) e (fsLog h u') + coneIntegral h W (e + 1) (fsLog h u) =
        cycleIntegral h (divCycle W u') e (fsLog h u) + coneIntegral h W (e + 1) (fsLog h u')
end
end GroundTheory.Heights₂.Heights



-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ContinuousBicharacterWeilSetup
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ContinuousBicharacterWeilSetup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:08:04.188811+00:00
-- url     : https://prove2.me/theorems/0d73d850-d30c-4254-9cb9-bdfa19c466ab
-- title:
--   Continuous Bicharacter Weil Setup
-- statement:
--   Definitions and structural lemmas for Continuous Bicharacter Weil Setup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ContinuousBicharacterWeilSetup.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExpSeriesContDiffAndHasDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CharSeriesExistsNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPosMulNormSqLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
namespace GlobalTheory.HeisenbergGaussianSeries
noncomputable def series {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℝ V]
    (p : G →+ V) (ι : V →+ G) (β : G → G → ℂ) (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (Γ : AddSubgroup G) (χ : G → ℂ) (a : V) (w : G) : ℂ :=
  ∑' g : Γ, β g w * β (ι a) (g + w) * χ (g + w) *
    Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ))
section
variable {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℝ V]
    {p : G →+ V} {ι : V →+ G} {β : G → G → ℂ} {om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {J : V →ₗ[ℝ] V}
    {Γ : AddSubgroup G} {χ : G → ℂ}
end
end GlobalTheory.HeisenbergGaussianSeries



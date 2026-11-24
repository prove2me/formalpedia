-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_HermAbs
-- name    : Development_WeilBound_ThetaLifts_LatticeBasics_HermAbs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:11.817513+00:00
-- url     : https://prove2.me/theorems/c0e0074f-dfef-497b-8e02-3a38c781cb75
-- title:
--   Herm Abs
-- statement:
--   Definitions and structural lemmas for Herm Abs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/HermAbs.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_SpanOrbitStab
import Theorems.Thm_PositivityTheory_ThKF_Abs_span_orbit_stab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThK.Dbl.Herm
open scoped InnerProductSpace
open PositivityTheory.ThKF.Abs
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
def homsF {K : Type} [Group K] (κ : K →* Module.End ℂ U) (f : U) : Submodule ℂ (orb κ f →ₗ[ℂ] U) where
  carrier := {L | ∀ k x, L ⟨κ k x.1, span_orbit_stab κ f k _ x.2⟩ = κ k (L x)}
  add_mem' := fun {a b} ha hb k x => by simp [ha k x, hb k x]
  zero_mem' := fun k x => by simp
  smul_mem' := fun c a ha k x => by simp [ha k x]
end GlobalTheory.ThK.Dbl.Herm
end



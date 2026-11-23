-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_FiniteDiscreteFamilies_PeakCone
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_FiniteDiscreteFamilies_PeakCone
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:23.641644+00:00
-- url     : https://prove2.me/theorems/cf6c64bc-4813-4c33-92b5-b6bd9240b0c2
-- title:
--   Peak Cone
-- statement:
--   Definitions and structural lemmas for Peak Cone, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/FiniteDiscreteFamilies/PeakCone.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.Rg.BcB.F.F5
def coneGL (n : ℕ) (M : ℤ) : Set (Fin n → ℤ) := {x | ∀ i j : Fin n, i < j → x j + M ≤ x i}
def evalGL {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ) (ξ : Fin n → ℂˣ) : ℂ :=
  c.sum fun x a => a * ((∏ i, ξ i ^ x i : ℂˣ) : ℂ)
def PeakCone : Prop := ∀ (n : ℕ) (M : ℤ) (α : Fin n → ℂˣ) (S : Finset (Fin n → ℂˣ)), α ∉ S →
  ∃ c : (Fin n → ℤ) →₀ ℂ, (↑c.support ⊆ coneGL n M) ∧ evalGL c α = 1 ∧ ∀ β ∈ S, evalGL c β = 0
end PositivityTheory.Rg.BcB.F.F5
end



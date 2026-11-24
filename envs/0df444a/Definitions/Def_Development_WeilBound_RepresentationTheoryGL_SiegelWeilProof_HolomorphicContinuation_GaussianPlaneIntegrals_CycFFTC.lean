-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTC
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTC
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T13:26:26.048127+00:00
-- url     : https://prove2.me/theorems/d8e8e1c6-5abb-4b95-9ed6-f794e34f924a
-- title:
--   Cyc FFTC
-- statement:
--   Definitions and structural lemmas for Cyc FFTC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTC.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace PositivityTheory.Rg.Sw.FFTSteps.CycF
variable {m n : ℕ} (ε : Fin m → Bool)
def eqv : Fin m × Fin n × Bool ≃ VV (Rw ε false) n ⊕ VV (Rw ε true) n where
  toFun k := if h : ε k.1 = true then Sum.inr (if k.2.2 then Sum.inr (⟨k.1, h⟩, k.2.1) else Sum.inl (⟨k.1, h⟩, k.2.1))
    else Sum.inl (if k.2.2 then Sum.inr (⟨k.1, by simpa using h⟩, k.2.1) else Sum.inl (⟨k.1, by simpa using h⟩, k.2.1))
  invFun := Sum.elim (jv ε false) (jv ε true)
  left_inv k := by
    obtain ⟨a, i, t⟩ := k
    by_cases h : ε a = true <;> cases t <;> simp [h, jv]
  right_inv x := by
    rcases x with (⟨⟨a, ha⟩, i⟩ | ⟨⟨a, ha⟩, i⟩) | (⟨⟨a, ha⟩, i⟩ | ⟨⟨a, ha⟩, i⟩) <;> simp [jv, ha]
def Th : PX m n ≃ₐ[ℂ] MvPolynomial (VV (Rw ε false) n) (PV (Rw ε true) (Fin n) (Fin n)) :=
  (renameEquiv ℂ (eqv ε)).trans (sumAlgEquiv ℂ _ _)
variable {ε}
end PositivityTheory.Rg.Sw.FFTSteps.CycF



-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularDirectionalJet
-- name    : CK_GeneralCK_Certificates_E8TAxisRegularDirectionalJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:34:33.57807+00:00
-- url     : https://prove2.me/theorems/d73eaf26-f0f0-4041-93c6-0b1f6dd53543
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisRegularDirectionalJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisRegularDirectionalJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisRegularDirectionalJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisRegularDirectionalJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisRegularDirectionalJet.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularGermJet

-- ===== source module GeneralCK.Certificates.E8TAxisRegularDirectionalJet =====
section

/-! Directional order-four jet for the regular inverse, including `t = 0`. -/

namespace GeneralCK.Certificates.E8TAxisRegularDirectionalJet

open GeneralCK Set
open E8TAxisDeltaDirectionalJet E8TAxisRegularGermJet

noncomputable def regularQPrimeJet : Jet5 := shift regularQJet

def InputsInRange (s t : ℝ) : Prop :=
  (t = 0 ∨ t ∈ e8SlopeRange) ∧ 2 * s + t ∈ e8SlopeRange ∧
    s + t ∈ e8SlopeRange ∧ s ∈ e8SlopeRange

noncomputable def deltaTJet (s0 t0 ds dt : ℝ) : Jet5 :=
  deltaTGraph
    (affine regularQJet t0 dt)
    (affine regularQJet (2 * s0 + t0) (2 * ds + dt))
    (affine regularQJet (s0 + t0) (ds + dt))
    (affine regularQJet s0 ds)
    (affine regularQPrimeJet t0 dt)
    (affine regularQPrimeJet (2 * s0 + t0) (2 * ds + dt))
    (affine regularQPrimeJet (s0 + t0) (ds + dt))

theorem regularQPrimeJet_sound4At {y : ℝ} (hy : y = 0 ∨ y ∈ e8SlopeRange) :
    Sound4At regularQPrimeJet y :=
  sound4At_shift (regularQJet_soundAt hy)

theorem deltaTJet_sound4At {s0 t0 ds dt u : ℝ}
    (h : InputsInRange (s0 + ds * u) (t0 + dt * u)) :
    Sound4At (deltaTJet s0 t0 ds dt) u := by
  have hB : (2 * s0 + t0) + (2 * ds + dt) * u ∈ e8SlopeRange := by
    rw [show (2 * s0 + t0) + (2 * ds + dt) * u =
      2 * (s0 + ds * u) + (t0 + dt * u) by ring]
    exact h.2.1
  have hC : (s0 + t0) + (ds + dt) * u ∈ e8SlopeRange := by
    rw [show (s0 + t0) + (ds + dt) * u =
      (s0 + ds * u) + (t0 + dt * u) by ring]
    exact h.2.2.1
  exact sound4At_deltaTGraph
    (sound4At_of_soundAt (regularQJet_soundAt h.1)).affine
    (sound4At_of_soundAt (regularQJet_soundAt_of_mem hB)).affine
    (sound4At_of_soundAt (regularQJet_soundAt_of_mem hC)).affine
    (sound4At_of_soundAt (regularQJet_soundAt_of_mem h.2.2.2)).affine
    (regularQPrimeJet_sound4At h.1).affine
    (regularQPrimeJet_sound4At (Or.inr hB)).affine
    (regularQPrimeJet_sound4At (Or.inr hC)).affine

theorem deltaTJet_sound4On {s0 t0 ds dt : ℝ} {S : Set ℝ}
    (h : ∀ u ∈ S, InputsInRange (s0 + ds * u) (t0 + dt * u)) :
    Sound4On (deltaTJet s0 t0 ds dt) S :=
  fun u hu => deltaTJet_sound4At (h u hu)

theorem deltaTJet_d0_eq_regular {s0 t0 ds dt u : ℝ}
    (h : InputsInRange (s0 + ds * u) (t0 + dt * u)) :
    (deltaTJet s0 t0 ds dt).d0 u =
      e8RegularDeltaT (s0 + ds * u) (t0 + dt * u) := by
  have hB : (2 * s0 + t0) + (2 * ds + dt) * u =
      2 * (s0 + ds * u) + (t0 + dt * u) := by ring
  have hC : (s0 + t0) + (ds + dt) * u =
      (s0 + ds * u) + (t0 + dt * u) := by ring
  have hregB : DifferentiableAt ℝ e8RegularQ (2 * (s0 + ds*u) + (t0 + dt*u)) := by
    exact (e8RegularQ_contDiffAt_of_mem h.2.1).differentiableAt (by norm_num)
  have hregC : DifferentiableAt ℝ e8RegularQ ((s0 + ds*u) + (t0 + dt*u)) := by
    exact (e8RegularQ_contDiffAt_of_mem h.2.2.1).differentiableAt (by norm_num)
  have hregA : DifferentiableAt ℝ e8RegularQ (t0 + dt*u) := by
    rcases h.1 with hzero | hpos
    · simpa [hzero] using hasDerivAt_e8RegularQ_zero.differentiableAt
    · exact (e8RegularQ_contDiffAt_of_mem hpos).differentiableAt (by norm_num)
  rw [e8RegularDeltaT, deriv_e8Delta_right e8RegularQ _ _ hregB hregC hregA]
  dsimp only [deltaTJet, deltaTGraph, E8TAxisDeltaDirectionalJet.sub,
    Jet5.add, Jet5.neg, Jet5.mul, affine, regularQPrimeJet, shift]
  rw [hB, hC, regularQJet_d0_eq_regular, regularQJet_d0_eq_regular,
    regularQJet_d0_eq_regular, regularQJet_d0_eq_regular,
    regularQJet_d1_eq_deriv h.1,
    regularQJet_d1_eq_deriv (Or.inr h.2.1),
    regularQJet_d1_eq_deriv (Or.inr h.2.2.1)]
  simp only [e8DeltaDerivT]
  ring

#print axioms deltaTJet_sound4On
#print axioms deltaTJet_d0_eq_regular

end GeneralCK.Certificates.E8TAxisRegularDirectionalJet

end



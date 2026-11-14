-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.rts_smoothing_covariance_improves_psd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:40:30.269241+00:00
-- url     : https://prove2.me/submissions/eb080716-2fcc-47dd-a0b2-7936f9123143

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix MeasureTheory
open scoped BigOperators Topology

theorem solution
    (n : ℕ)
    (J Pf Ppred Pnext Psmooth : Matrix (Fin n) (Fin n) ℝ)
    (hupdate : Psmooth = Pf + J * (Pnext - Ppred) * J.transpose)
    (hnext : ∀ v : Fin n → ℝ,
      0 ≤ ∑ i : Fin n, v i * ((Ppred - Pnext).mulVec v) i) :
    ∀ v : Fin n → ℝ,
      0 ≤ ∑ i : Fin n, v i * ((Pf - Psmooth).mulVec v) i := by
  intro v
  have hdiff : Pf - Psmooth = J * (Ppred - Pnext) * J.transpose := by
    rw [hupdate]
    noncomm_ring
  rw [hdiff]
  change 0 ≤ v ⬝ᵥ ((J * (Ppred - Pnext) * J.transpose) *ᵥ v)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec]
  rw [← Matrix.mulVec_transpose J v]
  simpa only [dotProduct] using hnext (J.transpose *ᵥ v)

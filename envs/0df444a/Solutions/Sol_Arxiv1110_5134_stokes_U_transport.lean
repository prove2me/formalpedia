-- Prove2me | solution 1 for Arxiv1110_5134.stokes_U_transport
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T08:17:39.282049+00:00
-- url     : https://prove2.me/submissions/5bc68575-01bd-4045-95cc-5f6b0a009349

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology Arxiv1110_5134
open scoped Matrix

theorem solution (n I χ ψ : ℝ → ℝ) (κ s : ℝ) (hn : 0 < n s)
    (hI : HasDerivAt (fun t => I t / n t ^ 2) 0 s) (hχ : HasDerivAt χ 0 s)
    (hψ : HasDerivAt ψ κ s) :
    HasDerivAt (fun t => stokesVec (I t) (χ t) (ψ t) 2 / n t ^ 2)
      (I s * Real.cos (2 * χ s) / n s ^ 2 * (2 * Real.cos (2 * ψ s) * κ)) s ∧
    I s * Real.cos (2 * χ s) / n s ^ 2 * (2 * Real.cos (2 * ψ s) * κ) =
      I s * Real.cos (2 * χ s) * Real.cos (2 * ψ s) / n s ^ 2 * (2 * κ) ∧
    I s * Real.cos (2 * χ s) * Real.cos (2 * ψ s) / n s ^ 2 * (2 * κ) =
      2 * κ * (stokesVec (I s) (χ s) (ψ s) 1 / n s ^ 2) := by
  have hcosχ : HasDerivAt (fun t => Real.cos (2 * χ t)) (-Real.sin (2 * χ s) * (2 * 0)) s :=
    (hχ.const_mul 2).cos
  have hIC : HasDerivAt (fun t => I t * Real.cos (2 * χ t) / n t ^ 2) 0 s := by
    have hfn : (fun t => I t * Real.cos (2 * χ t) / n t ^ 2) =
        ((fun t => I t / n t ^ 2) * fun t => Real.cos (2 * χ t)) := by
      ext t
      simp [Pi.mul_apply]
      ring
    have hval : (0 : ℝ) =
        0 * Real.cos (2 * χ s) + I s / n s ^ 2 * (-Real.sin (2 * χ s) * (2 * 0)) := by
      ring
    rw [hfn, hval]
    exact hI.mul hcosχ
  have hsinψ : HasDerivAt (fun t => Real.sin (2 * ψ t)) (Real.cos (2 * ψ s) * (2 * κ)) s :=
    (hψ.const_mul 2).sin
  have hU : HasDerivAt (fun t => stokesVec (I t) (χ t) (ψ t) 2 / n t ^ 2)
      (I s * Real.cos (2 * χ s) / n s ^ 2 * (2 * Real.cos (2 * ψ s) * κ)) s := by
    have hfn : (fun t => stokesVec (I t) (χ t) (ψ t) 2 / n t ^ 2) =
        ((fun t => I t * Real.cos (2 * χ t) / n t ^ 2) * fun t => Real.sin (2 * ψ t)) := by
      ext t
      simp [stokesVec, Pi.mul_apply]
      ring
    have hval : I s * Real.cos (2 * χ s) / n s ^ 2 * (2 * Real.cos (2 * ψ s) * κ) =
        0 * Real.sin (2 * ψ s) + I s * Real.cos (2 * χ s) / n s ^ 2 * (Real.cos (2 * ψ s) * (2 * κ)) := by
      ring
    rw [hfn, hval]
    exact hIC.mul hsinψ
  refine ⟨hU, by ring, ?_⟩
  simp [stokesVec]
  ring

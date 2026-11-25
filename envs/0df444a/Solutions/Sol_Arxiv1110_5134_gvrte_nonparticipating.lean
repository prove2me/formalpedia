-- Prove2me | solution 1 for Arxiv1110_5134.gvrte_nonparticipating
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T08:17:40.27623+00:00
-- url     : https://prove2.me/submissions/7f1bd725-2d4b-4c36-814a-8c1fa23dba2d

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic
import Theorems.Thm_Arxiv1110_5134_stokes_V_invariant
import Theorems.Thm_Arxiv1110_5134_stokes_Q_transport
import Theorems.Thm_Arxiv1110_5134_stokes_U_transport

open MeasureTheory Filter Topology Arxiv1110_5134
open scoped Matrix

theorem solution (n I χ ψ : ℝ → ℝ) (κ s : ℝ) (hn : 0 < n s)
    (hI : HasDerivAt (fun t => I t / n t ^ 2) 0 s) (hχ : HasDerivAt χ 0 s)
    (hψ : HasDerivAt ψ κ s) :
    DifferentiableAt ℝ (fun t => (n t ^ 2)⁻¹ • stokesVec (I t) (χ t) (ψ t)) s ∧
    transportOp n (fun t => stokesVec (I t) (χ t) (ψ t)) s +
      rytovMatrix κ *ᵥ stokesVec (I s) (χ s) (ψ s) = 0 := by
  let f : ℝ → Stokes := fun t => (n t ^ 2)⁻¹ • stokesVec (I t) (χ t) (ψ t)
  let d : Stokes :=
    ![0,
      -2 * κ * (stokesVec (I s) (χ s) (ψ s) 2 / n s ^ 2),
      2 * κ * (stokesVec (I s) (χ s) (ψ s) 1 / n s ^ 2),
      0]
  have hQ_all := stokes_Q_transport n I χ ψ κ s hn hI hχ hψ
  have hU_all := stokes_U_transport n I χ ψ κ s hn hI hχ hψ
  have hV := stokes_V_invariant n I χ ψ s hn hI hχ
  have hQ : HasDerivAt (fun t => stokesVec (I t) (χ t) (ψ t) 1 / n t ^ 2)
      (-2 * κ * (stokesVec (I s) (χ s) (ψ s) 2 / n s ^ 2)) s := by
    rw [← hQ_all.2.2]
    exact hQ_all.2.1
  have hU : HasDerivAt (fun t => stokesVec (I t) (χ t) (ψ t) 2 / n t ^ 2)
      (2 * κ * (stokesVec (I s) (χ s) (ψ s) 1 / n s ^ 2)) s := by
    rw [← hU_all.2.2, ← hU_all.2.1]
    exact hU_all.1
  have hf : HasDerivAt f d s := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · have hfn : (fun t => f t 0) = (fun t => I t / n t ^ 2) := by
        ext t; simp [f, stokesVec, div_eq_inv_mul]
      change HasDerivAt (fun t => f t 0) (d 0) s
      rw [hfn]
      exact hI
    · have hfn : (fun t => f t 1) = (fun t => stokesVec (I t) (χ t) (ψ t) 1 / n t ^ 2) := by
        ext t; simp [f, div_eq_inv_mul]
      change HasDerivAt (fun t => f t 1) (d 1) s
      rw [hfn]
      exact hQ
    · have hfn : (fun t => f t 2) = (fun t => stokesVec (I t) (χ t) (ψ t) 2 / n t ^ 2) := by
        ext t; simp [f, div_eq_inv_mul]
      change HasDerivAt (fun t => f t 2) (d 2) s
      rw [hfn]
      exact hU
    · have hfn : (fun t => f t 3) = (fun t => stokesVec (I t) (χ t) (ψ t) 3 / n t ^ 2) := by
        ext t; simp [f, div_eq_inv_mul]
      change HasDerivAt (fun t => f t 3) (d 3) s
      rw [hfn]
      exact hV
  refine ⟨hf.differentiableAt, ?_⟩
  have hn2 : n s ^ 2 ≠ 0 := pow_ne_zero 2 hn.ne'
  have htr : transportOp n (fun t => stokesVec (I t) (χ t) (ψ t)) s = (n s ^ 2) • d := by
    change (n s ^ 2) • deriv f s = (n s ^ 2) • d
    rw [hf.deriv]
  rw [htr]
  ext i
  fin_cases i <;>
    simp [d, rytovMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    field_simp [hn2] <;>
    ring

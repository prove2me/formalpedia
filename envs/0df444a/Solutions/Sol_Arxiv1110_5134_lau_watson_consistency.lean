-- Prove2me | solution 1 for Arxiv1110_5134.lau_watson_consistency
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T08:37:16.531557+00:00
-- url     : https://prove2.me/submissions/79cbe9d0-76d5-47c8-b793-9792dfc66269

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology Arxiv1110_5134
open scoped Matrix

theorem solution (n : ℝ → ℝ) (S : ℝ → Stokes) (s ke κ : ℝ)
    (hn : 0 < n s) (hnd : DifferentiableAt ℝ n s) (hS : DifferentiableAt ℝ S s) :
    -deriv (fun t => Real.log (n t ^ 2)) s = deriv (fun t => Real.log ((n t ^ 2)⁻¹)) s ∧
    deriv (fun t => Real.log ((n t ^ 2)⁻¹)) s = n s ^ 2 * deriv (fun t => (n t ^ 2)⁻¹) s ∧
    deriv S s + (ke - deriv (fun t => Real.log (n t ^ 2)) s) • S s + rytovMatrix κ *ᵥ S s =
      transportOp n S s + (ke • (1 : Matrix (Fin 4) (Fin 4) ℝ) + rytovMatrix κ) *ᵥ S s := by
  have hn2 : n s ^ 2 ≠ 0 := pow_ne_zero 2 hn.ne'
  have hn2_inv : (n s ^ 2)⁻¹ ≠ 0 := inv_ne_zero hn2
  have hsq : HasDerivAt (fun t => n t ^ 2) (2 * n s ^ (2 - 1) * deriv n s) s :=
    hnd.hasDerivAt.pow 2
  have hinv : HasDerivAt (fun t => (n t ^ 2)⁻¹)
      (-(2 * n s ^ (2 - 1) * deriv n s) / (n s ^ 2) ^ 2) s :=
    hsq.inv hn2
  have hlog : HasDerivAt (fun t => Real.log (n t ^ 2))
      ((2 * n s ^ (2 - 1) * deriv n s) / n s ^ 2) s :=
    hsq.log hn2
  have hloginv : HasDerivAt (fun t => Real.log ((n t ^ 2)⁻¹))
      ((-(2 * n s ^ (2 - 1) * deriv n s) / (n s ^ 2) ^ 2) / (n s ^ 2)⁻¹) s :=
    hinv.log hn2_inv
  have h1 : -deriv (fun t => Real.log (n t ^ 2)) s = deriv (fun t => Real.log ((n t ^ 2)⁻¹)) s := by
    rw [hlog.deriv, hloginv.deriv]
    field_simp [hn2]
  have h2 : deriv (fun t => Real.log ((n t ^ 2)⁻¹)) s = n s ^ 2 * deriv (fun t => (n t ^ 2)⁻¹) s := by
    rw [hloginv.deriv, hinv.deriv]
    field_simp [hn2]
  refine ⟨h1, h2, ?_⟩
  have hprod := hinv.smul hS.hasDerivAt
  have hd : deriv (fun t => (n t ^ 2)⁻¹ • S t) s =
      (n s ^ 2)⁻¹ • deriv S s + (-(2 * n s ^ (2 - 1) * deriv n s) / (n s ^ 2) ^ 2) • S s :=
    hprod.deriv
  have htr : transportOp n S s =
      deriv S s + (n s ^ 2 * deriv (fun t => (n t ^ 2)⁻¹) s) • S s := by
    unfold transportOp
    rw [hd, hinv.deriv]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp [hn2]
  rw [htr, ← h2, ← h1]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  ring
